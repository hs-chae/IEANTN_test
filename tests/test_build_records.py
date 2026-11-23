"""Computed results: `reason`, `computation`, and the build records `check` holds them to."""
from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import pathlib
import sys

from test_ieantn import FixtureRepo, ieantn

# `build_record` imports `ieantn` by name; give it the instance the fixture repoints.
sys.modules["ieantn"] = ieantn
_SPEC = importlib.util.spec_from_file_location(
    "build_record", pathlib.Path(__file__).resolve().parent.parent / "scripts" / "build_record.py"
)
assert _SPEC and _SPEC.loader
build_record = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(build_record)

CONCLUSION = """
- id: main
  declaration: {node}.main
  challenge: {node}.challenge_main
  imports: []
  imports_status: none
  issue: 7
  justifications:
    - id: port
      kind: KIND
REASON      note: >-
        Finite checks run by native_decide.
COMPUTATION  designated: port
"""


def conclusion(kind: str = "lean-noncompliant", reason: str | None = "native_decide",
               computation: str = "") -> str:
    text = CONCLUSION.replace("KIND", kind)
    text = text.replace("REASON", f"      reason: {reason}\n" if reason is not None else "")
    return text.replace("COMPUTATION", computation)


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class TestReasonAndRecords(FixtureRepo):
    def solution(self, node_id: str = "A.v1") -> pathlib.Path:
        directory = self.root / "Solutions" / node_id
        (directory / "c").mkdir(parents=True, exist_ok=True)
        (directory / "Solution.lean").write_text("-- the proof\n", encoding="utf-8")
        (directory / "c" / "sum.c").write_text("int main(void) { return 0; }\n", encoding="utf-8")
        return directory

    def record(self, key: str = "A.v1.main", *, natives: int = 1, status: str = "passed",
               matches: bool = True) -> pathlib.Path:
        directory = self.root / "Solutions" / key.rsplit(".", 1)[0]
        files = [directory / "Solution.lean", directory / "c" / "sum.c"]
        record = {
            "schema": ieantn.BUILD_RECORD_SCHEMA, "conclusion": key, "status": status,
            "reasons": [] if status == "passed" else ["`lake build` exited 1"],
            "statement_matches_challenge": matches,
            "axioms": {"standard": ["propext"], "other": [],
                       "native_decide": [{"axiom": f"t._native.native_decide.ax_1_{i}",
                                          "theorem": "t", "file": "Solution.lean", "line": 1,
                                          "proposition": "true = true"} for i in range(natives)]},
            "files": [{"path": ieantn.rel(path), "sha256": sha(path)} for path in files],
        }
        path = ieantn.build_record_path(key)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(record), encoding="utf-8")
        return path

    def test_lean_noncompliant_must_say_why_there_is_no_receipt(self) -> None:
        self.write_node("A.v1", conclusion(reason=None))
        self.solution()
        self.assertFalse(ieantn.check_computations())

    def test_the_reason_must_be_one_of_the_two_obstacles(self) -> None:
        self.write_node("A.v1", conclusion(reason="too-hard"))
        self.solution()
        self.assertFalse(ieantn.check_computations())

    def test_reason_belongs_only_on_lean_noncompliant(self) -> None:
        self.write_node("A.v1", conclusion(kind="literature", reason="native_decide"))
        self.assertFalse(ieantn.check_computations())

    def test_no_record_is_shown_as_not_built_and_does_not_fail(self) -> None:
        self.write_node("A.v1", conclusion())
        self.solution()
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            self.assertTrue(ieantn.check_computations())
        self.assertIn("A.v1.main", printed.getvalue())
        self.assertEqual(ieantn.build_record_state("A.v1.main")[0], "not built")

    def test_a_current_record_passes(self) -> None:
        self.write_node("A.v1", conclusion())
        self.solution()
        self.record()
        self.assertTrue(ieantn.check_computations())
        state, detail = ieantn.build_record_state("A.v1.main")
        self.assertEqual(state, "current")
        self.assertIn("1 native_decide step", detail)

    def test_an_edited_program_makes_the_record_stale(self) -> None:
        """The point of hashing: a changed C file no longer matches what was compiled."""
        self.write_node("A.v1", conclusion())
        directory = self.solution()
        self.record()
        (directory / "c" / "sum.c").write_text("int main(void) { return 1; }\n", encoding="utf-8")
        self.assertFalse(ieantn.check_computations())
        state, detail = ieantn.build_record_state("A.v1.main")
        self.assertEqual(state, "stale")
        self.assertIn("Solutions/A.v1/c/sum.c", detail)

    def test_a_deleted_file_makes_the_record_stale(self) -> None:
        self.write_node("A.v1", conclusion())
        directory = self.solution()
        self.record()
        (directory / "Solution.lean").unlink()
        self.assertEqual(ieantn.build_record_state("A.v1.main")[0], "stale")

    def test_a_failed_record_fails(self) -> None:
        self.write_node("A.v1", conclusion())
        self.solution()
        self.record(status="failed")
        self.assertFalse(ieantn.check_computations())

    def test_a_record_whose_statement_differs_fails(self) -> None:
        self.write_node("A.v1", conclusion())
        self.solution()
        self.record(matches=False)
        self.assertEqual(ieantn.build_record_state("A.v1.main")[0], "failed")

    def test_reason_native_decide_needs_a_native_step(self) -> None:
        self.write_node("A.v1", conclusion(reason="native_decide"))
        self.solution()
        self.record(natives=0)
        self.assertFalse(ieantn.check_computations())

    def test_native_steps_contradict_workflow_cannot_run(self) -> None:
        self.write_node("A.v1", conclusion(reason="workflow-cannot-run"))
        self.solution()
        self.record(natives=2)
        self.assertFalse(ieantn.check_computations())

    def test_a_record_for_no_conclusion_fails(self) -> None:
        self.write_node("A.v1", conclusion())
        self.solution()
        self.record("A.v1.elsewhere")
        self.assertFalse(ieantn.check_computations())

    def test_status_and_report_show_the_build_state(self) -> None:
        self.write_node("A.v1", conclusion())
        self.solution()
        self.record()
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            ieantn.report()
        self.assertIn("[lean-noncompliant: native_decide, build record current]",
                      printed.getvalue())


class TestComputationRecords(FixtureRepo):
    def program(self) -> pathlib.Path:
        path = self.root / "Solutions" / "A.v1" / "c" / "sum.c"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("int main(void) { return 0; }\n", encoding="utf-8")
        return path

    def numerical(self, computation: str) -> None:
        # `write_node` formats `{node}` into the text, so YAML's own braces are escaped.
        escaped = computation.replace("{", "{{").replace("}", "}}")
        self.write_node("A.v1", conclusion(kind="numerical", reason=None, computation=escaped))

    def test_a_matching_program_hash_passes(self) -> None:
        program = self.program()
        self.numerical("      computation:\n        files:\n"
                       f"          - {{path: Solutions/A.v1/c/sum.c, role: program, sha256: {sha(program)}}}\n"
                       "        output: '42'\n")
        self.assertTrue(ieantn.check_computations())

    def test_an_edited_program_fails(self) -> None:
        program = self.program()
        self.numerical("      computation:\n        files:\n"
                       f"          - {{path: Solutions/A.v1/c/sum.c, role: program, sha256: {sha(program)}}}\n")
        program.write_text("int main(void) { return 1; }\n", encoding="utf-8")
        self.assertFalse(ieantn.check_computations())

    def test_a_record_must_name_something(self) -> None:
        self.numerical("      computation:\n        output: '42'\n")
        self.assertFalse(ieantn.check_computations())

    def test_paths_stay_inside_the_repository(self) -> None:
        self.numerical("      computation:\n        files:\n"
                       f"          - {{path: ../outside.c, role: program, sha256: {'0' * 64}}}\n")
        self.assertFalse(ieantn.check_computations())

    def test_roles_are_a_fixed_vocabulary(self) -> None:
        program = self.program()
        self.numerical("      computation:\n        files:\n"
                       f"          - {{path: Solutions/A.v1/c/sum.c, role: magic, sha256: {sha(program)}}}\n")
        self.assertFalse(ieantn.check_computations())

    def test_an_external_computation_needs_a_checksum_or_says_there_is_none(self) -> None:
        self.numerical("      computation:\n        external:\n"
                       "          - {url: 'https://example.org/zeros'}\n")
        self.assertFalse(ieantn.check_computations())
        self.numerical("      computation:\n        external:\n"
                       "          - {url: 'https://example.org/zeros', checksum: none published}\n")
        self.assertTrue(ieantn.check_computations())


class TestBuildRecordHelpers(FixtureRepo):
    def package(self) -> pathlib.Path:
        package = self.root / "Solutions" / "A.v1"
        (package / "Lib").mkdir(parents=True, exist_ok=True)
        (package / "c").mkdir(exist_ok=True)
        (package / "lakefile.toml").write_text('name = "a"\n', encoding="utf-8")
        (package / "c" / "sum.c").write_text("int x;\n", encoding="utf-8")
        (package / "Lib" / "Program.lean").write_text(
            'def source : String := include_str ".."/"c"/"sum.c"\n', encoding="utf-8")
        (package / "Lib" / "Plain.lean").write_text("def two : Nat := 2\n", encoding="utf-8")
        return package

    def test_include_str_paths_resolve_against_the_embedding_file(self) -> None:
        package = self.package()
        self.assertEqual(build_record.embedded_paths(package / "Lib" / "Program.lean"),
                         [(package / "c" / "sum.c").resolve()])
        self.assertEqual(build_record.embedded_paths(package / "Lib" / "Plain.lean"), [])

    def test_only_modules_that_embed_a_file_are_forced_to_recompile(self) -> None:
        package = self.package()
        built = package / ".lake" / "build" / "lib" / "lean" / "Lib"
        built.mkdir(parents=True)
        for stem in ("Program", "Plain"):
            for suffix in (".olean", ".ilean", ".trace", ".olean.hash"):
                (built / f"{stem}{suffix}").write_text("x", encoding="utf-8")
        forced = build_record.force_rebuild([package])
        self.assertEqual(forced, ["Solutions/A.v1/Lib/Program.lean"])
        self.assertEqual(sorted(p.name for p in built.iterdir()),
                         ["Plain.ilean", "Plain.olean", "Plain.olean.hash", "Plain.trace"])

    def test_a_nested_package_is_not_scanned_as_part_of_its_parent(self) -> None:
        package = self.package()
        nested = package / "Nested"
        nested.mkdir()
        (nested / "lakefile.toml").write_text('name = "n"\n', encoding="utf-8")
        (nested / "Inner.lean").write_text("def one : Nat := 1\n", encoding="utf-8")
        names = [p.name for p in build_record.package_lean_files(package)]
        self.assertNotIn("Inner.lean", names)

    def test_only_the_generated_native_decide_shape_counts_as_a_native_step(self) -> None:
        package = self.package()
        source = package / "Lib" / "Checks.lean"
        line = "theorem t : f = true := by native_decide"
        source.write_text(line + "\n", encoding="utf-8")
        column = line.index("native_decide")
        olean = str(package / ".lake" / "build" / "lib" / "lean" / "Lib" / "Checks.olean")
        native = {"tactic": "native_decide", "decl": "t", "decl_exists": True,
                  "decl_is_theorem": True, "decl_module": "Lib.Checks", "eq_true_shape": True,
                  "has_fvar_or_mvar": False, "decided_prop_pp": "f = true"}
        at_token = {"start_line": 1, "start_col": column, "end_line": 1,
                    "end_col": column + len("native_decide")}
        elsewhere = {"start_line": 1, "start_col": 0, "end_line": 1, "end_col": 7}
        data = {
            "project_modules": [{"module": "Lib.Checks", "olean": olean}],
            "axioms": [
                {"name": "propext", "module": "Init.Core"},
                {"name": "t._native.native_decide.ax_1_1", "module": "Lib.Checks",
                 "range": at_token, "native": native},
                {"name": "t._native.native_decide.ax_1_2", "module": "Lib.Checks",
                 "range": elsewhere, "native": native},
                {"name": "sorryAx", "module": "Init.Prelude"},
            ],
        }
        standard, natives, other = build_record.classify_axioms(data)
        self.assertEqual(standard, ["propext"])
        self.assertEqual([n["axiom"] for n in natives], ["t._native.native_decide.ax_1_1"])
        self.assertEqual(sorted(o["axiom"] for o in other),
                         ["sorryAx", "t._native.native_decide.ax_1_2"])
