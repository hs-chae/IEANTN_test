"""Unit tests for the local native-assisted gate policy (scripts/native_assisted/native_assisted_check.py).

Pure Python: synthetic extractor output, temporary source files, no Lean. The Lean-level
negative controls (real mutated modules) live in scripts/native_assisted/controls.py.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "native_assisted_check", ROOT / "scripts" / "native_assisted" / "native_assisted_check.py")
NA = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(NA)
SEM = json.loads((ROOT / "scripts" / "native_assisted" / "semantics.json").read_text())

STD = [{"name": n, "module": m, "range": None} for n, m in
       (("propext", "Init.Core"), ("Classical.choice", "Init.Prelude"), ("Quot.sound", "Init.Prelude"))]


class Fixture:
    """A fake package: one project module whose source has a native_decide token on line 3."""

    def __init__(self, source_text: str | None = None):
        self.tmp = tempfile.TemporaryDirectory()
        self.pkg = pathlib.Path(self.tmp.name) / "pkg"
        (self.pkg / ".lake" / "build" / "lib" / "lean" / "Demo").mkdir(parents=True)
        (self.pkg / "Demo").mkdir()
        self.src = self.pkg / "Demo" / "Cert.lean"
        self.src.write_text(source_text if source_text is not None else
                            "import Demo.Base\n\ntheorem check : decide (2 + 2 = 4) = true := by native_decide\n"
                            "axiom bogus._native.native_decide.ax_1_1 : true = true\n")
        self.olean = str(self.pkg / ".lake" / "build" / "lib" / "lean" / "Demo" / "Cert.olean")
        self.csrc = self.pkg / "prog.c"
        self.csrc.write_text("double f(void) { return 1.0; }\n")
        self.lit = self.pkg / "lit.txt"
        self.lit.write_text(self.csrc.read_text())

    def native(self, name="Demo.check._native.native_decide.ax_1_1", decl="Demo.check",
               line=3, col=None, end=None, impls=None, shape=True):
        if col is None:  # the real column of the `native_decide` token on that line
            col = self.src.read_text().split("\n")[line - 1].index("native_decide")
            end = col + len("native_decide")
        return {"name": name, "module": "Demo.Cert", "type_pp": "decide (2+2=4) = true",
                "range": {"start_line": line, "start_col": col, "end_line": line, "end_col": end},
                "native": {"tactic": "native_decide", "decl": decl, "decl_exists": True,
                           "decl_is_theorem": True, "decl_module": "Demo.Cert",
                           "eq_true_shape": shape, "has_fvar_or_mvar": False,
                           "decided_prop_pp": "2 + 2 = 4", "implementations": impls or []}}

    def extract(self, axioms, consts=None, literals=None, etype="Demo.claim"):
        return {"endpoint": "Demo.challenge_claim", "endpoint_kind": "theorem",
                "endpoint_module": "Demo.Cert", "endpoint_type_all": etype,
                "project_modules": [{"module": "Demo.Cert", "olean": self.olean}],
                "axioms": STD + axioms, "project_constants": consts or [],
                "string_literals": literals or []}

    def close(self):
        self.tmp.cleanup()


def program_consts():
    """A minimal source-linked shape: literal, association, execution witness, correctness."""
    return [
        {"name": "Demo.src", "kind": "def", "type_mentions": [], "value_mentions": []},
        {"name": "Demo.source_check", "kind": "theorem",
         "type_mentions": ["ForwardRamanujan.sourceMatches", "Demo.src", "Demo.prog"]},
        {"name": "Demo.concrete_execution", "kind": "theorem",
         "type_mentions": ["ForwardRamanujan.Exec", "Demo.src", "Demo.prog"]},
        {"name": "ForwardRamanujan.source_linked_upper", "kind": "theorem", "type_mentions": []},
    ]


class TestAxiomPolicy(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()

    def tearDown(self):
        self.f.close()

    def test_allowed_native_fact_passes(self):
        r = NA.evaluate(self.f.extract([self.f.native()]), None, {}, SEM)
        self.assertEqual(r["status"], "passed", r["reasons"])
        self.assertEqual(r["axioms"]["native_fact_count"], 1)
        self.assertEqual(r["axioms"]["native_facts"][0]["token"], "native_decide")

    def test_custom_axiom_fails(self):
        ax = {"name": "Demo.myAxiom", "module": "Demo.Cert", "range": None}
        r = NA.evaluate(self.f.extract([ax]), None, {}, SEM)
        self.assertEqual(r["status"], "failed")
        self.assertIn("custom or unknown axiom", " ".join(r["reasons"]))

    def test_sorry_fails(self):
        r = NA.evaluate(self.f.extract([{"name": "sorryAx", "module": "Init.Prelude"}]), None, {}, SEM)
        self.assertEqual(r["status"], "failed")

    def test_native_named_axiom_without_native_decide_token_fails(self):
        # an `axiom` command given a native-looking name: its range points at the axiom command
        fake = self.f.native(name="bogus._native.native_decide.ax_1_1", decl="bogus", line=4,
                             col=0, end=50)
        r = NA.evaluate(self.f.extract([fake]), None, {}, SEM)
        self.assertEqual(r["status"], "failed")
        self.assertIn("does not point at a `native_decide` token", " ".join(r["reasons"]))

    def test_wrong_shape_fails(self):
        r = NA.evaluate(self.f.extract([self.f.native(shape=False)]), None, {}, SEM)
        self.assertEqual(r["status"], "failed")

    def test_project_implemented_by_reached_by_native_fails(self):
        impl = [{"name": "Demo.fastEval", "module": "Demo.Cert", "library": False,
                 "implemented_by": "Demo.fastEvalImpl", "extern": False}]
        r = NA.evaluate(self.f.extract([self.f.native(impls=impl)]), None, {}, SEM)
        self.assertEqual(r["status"], "failed")
        self.assertIn("implemented_by", " ".join(r["reasons"]))

    def test_unsafe_project_constant_fails(self):
        c = [{"name": "Demo.u", "kind": "def", "unsafe": True}]
        r = NA.evaluate(self.f.extract([], consts=c), None, {}, SEM)
        self.assertEqual(r["status"], "failed")

    def test_other_native_mechanism_blocks(self):
        r = NA.evaluate(self.f.extract([{"name": "Lean.ofReduceBool", "module": "Init.Core"}]),
                        None, {}, SEM)
        self.assertEqual(r["status"], "blocked")

    def test_unresolvable_source_fails(self):
        ex = self.f.extract([self.f.native()])
        ex["project_modules"] = [{"module": "Demo.Cert", "olean": "/nowhere/Demo/Cert.olean"}]
        r = NA.evaluate(ex, None, {}, SEM)
        self.assertEqual(r["status"], "failed")

    def test_challenge_type_mismatch_fails(self):
        ex = self.f.extract([self.f.native()])
        ch = {"endpoint": ex["endpoint"], "endpoint_type_all": "Demo.otherClaim"}
        r = NA.evaluate(ex, ch, {"challenge_decl": True}, SEM)
        self.assertEqual(r["status"], "failed")
        self.assertFalse(r["challenge_type_match"])


    def test_a_solution_module_named_challenge_is_not_the_challenge(self):
        """A solution may name its own module `….Challenge`; only the generated one counts."""
        ex = self.f.extract([self.f.native()])
        ex["endpoint_module"] = "RamanujanBudget.Challenge"
        ch = {"endpoint": ex["endpoint"], "endpoint_type_all": ex["endpoint_type_all"]}
        r = NA.evaluate(ex, ch, {"challenge_module": "IEANTN.Nodes.Demo.v1.Challenge"}, SEM)
        self.assertNotIn("endpoint resolved to the challenge itself, not a solution", r["reasons"])

    def test_the_generated_challenge_itself_fails(self):
        ex = self.f.extract([self.f.native()])
        ex["endpoint_module"] = "IEANTN.Nodes.Demo.v1.Challenge"
        ch = {"endpoint": ex["endpoint"], "endpoint_type_all": ex["endpoint_type_all"]}
        r = NA.evaluate(ex, ch, {"challenge_module": "IEANTN.Nodes.Demo.v1.Challenge"}, SEM)
        self.assertIn("endpoint resolved to the challenge itself, not a solution", r["reasons"])


class TestEvidenceMethod(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()
        self.lit = [{"name": "Demo.src", "file": str(self.f.lit)}]
        self.cfg = {"sources": [str(self.f.csrc.relative_to(NA.ROOT))
                                if self.f.csrc.is_relative_to(NA.ROOT) else str(self.f.csrc)]}

    def tearDown(self):
        self.f.close()

    def method(self, consts, literals, etype="Demo.claim", cfg=None):
        # point the configured source at an absolute path (ROOT / abs == abs)
        cfg = cfg or {"sources": [str(self.f.csrc)]}
        return NA.method_checks(self.f.extract([], consts=consts, literals=literals, etype=etype),
                                cfg, SEM)

    def test_full_program_link_is_lean_verified_program(self):
        m = self.method(program_consts(), self.lit)
        self.assertEqual(m["result"], "lean-verified-program", m)

    def test_source_hash_mismatch(self):
        self.f.csrc.write_text("double f(void) { return 2.0; }\n")
        m = self.method(program_consts(), self.lit)
        self.assertFalse(m["S_source_identity"]["ok"])
        self.assertEqual(m["result"], "not-program-verified")

    def test_missing_correctness_lemma(self):
        consts = [c for c in program_consts() if c["name"] != "ForwardRamanujan.source_linked_upper"]
        m = self.method(consts, self.lit)
        self.assertFalse(m["C_generic_correctness"]["ok"])
        self.assertEqual(m["result"], "not-program-verified")

    def test_numeric_inequality_without_source_link(self):
        m = self.method([{"name": "Demo.claim_by_norm_num", "kind": "theorem", "type_mentions": []}], [])
        self.assertEqual(m["result"], "not-program-verified")
        self.assertFalse(m["S_source_identity"]["ok"])

    def test_wrong_program_association(self):
        # association and execution facts exist, but about a literal that is not the configured C
        other = self.f.pkg / "other.txt"
        other.write_text("int main(void){return 0;}\n")
        m = self.method(program_consts(), [{"name": "Demo.src", "file": str(other)}])
        self.assertEqual(m["result"], "not-program-verified")

    def test_association_through_definitions(self):
        consts = program_consts()
        consts[1] = {"name": "Demo.source_check", "kind": "theorem", "type_mentions": ["Demo.checked"]}
        consts.append({"name": "Demo.checked", "kind": "def", "type_mentions": [],
                       "value_mentions": ["FKS2Scalar.tokens", "Demo.src"]})
        m = self.method(consts, self.lit)
        self.assertTrue(m["A_source_association"]["ok"], m)

    def test_program_level_endpoint_is_not_a_mathematical_statement(self):
        m = self.method(program_consts(), self.lit, etype="ForwardRamanujan.Exec Demo.src Demo.prog")
        self.assertFalse(m["M_mathematical_endpoint"]["ok"])
        self.assertEqual(m["result"], "not-program-verified")


class TestDyadicBackend(unittest.TestCase):
    """A generated Lean expression under a dyadic interval evaluator: no C file, pinned Lean sources."""

    SEM2 = {**SEM, "backends": {"lean-dyadic-expr": {"association": ["Demo.value"],
                                                     "execution": ["Demo.run"],
                                                     "correctness": ["Demo.sound"]}}}

    def setUp(self):
        self.f = Fixture()
        self.sha = hashlib.sha256(self.f.src.read_bytes()).hexdigest()

    def tearDown(self):
        self.f.close()

    def consts(self):
        return [
            {"name": "Demo.prog", "module": "Demo.Cert", "kind": "def", "type_mentions": [],
             "value_mentions": ["Demo.gen"]},
            {"name": "Demo.gen", "module": "Demo.Cert", "kind": "def", "type_mentions": [],
             "value_mentions": []},
            {"name": "Demo.gen_semantics", "module": "Demo.Cert", "kind": "theorem",
             "type_mentions": ["Demo.value", "Demo.gen"]},
            {"name": "Demo.checked", "module": "Demo.Cert", "kind": "theorem",
             "type_mentions": ["Demo.run", "Demo.prog"]},
            {"name": "Demo.sound", "module": "Demo.Cert", "kind": "theorem", "type_mentions": []},
        ]

    def spec(self, **over):
        d = {"backend": "lean-dyadic-expr", "program_constants": ["Demo.prog"],
             "program_sources": {str(self.f.src): self.sha}}
        d.update(over)
        return d

    def method(self, consts, backends, etype="Demo.claim", literals=None):
        return NA.method_checks(self.f.extract([], consts=consts, literals=literals or [],
                                               etype=etype), {"backends": backends}, self.SEM2)

    def test_pinned_program_with_association_execution_and_soundness(self):
        m = self.method(self.consts(), [self.spec()])
        self.assertEqual(m["result"], "lean-verified-program", m)

    def test_changed_program_source_fails_identity(self):
        self.f.src.write_text(self.f.src.read_text() + "-- edited\n")
        m = self.method(self.consts(), [self.spec()])
        self.assertFalse(m["S_source_identity"]["ok"])
        self.assertEqual(m["result"], "not-program-verified")

    def test_program_outside_the_proof_closure_fails(self):
        consts = [c for c in self.consts() if c["name"] != "Demo.prog"]
        m = self.method(consts, [self.spec()])
        self.assertEqual(m["result"], "not-program-verified")

    def test_unreviewed_backend_fails(self):
        m = self.method(self.consts(), [self.spec(backend="gpu-kernel")])
        self.assertEqual(m["result"], "not-program-verified")

    def test_every_backend_must_pass(self):
        lit = self.f.pkg / "lit.txt"
        good_c = {"backend": "restricted-c-binary64", "sources": [str(self.f.csrc)]}
        consts = self.consts() + program_consts()
        m = self.method(consts, [self.spec(), good_c],
                        literals=[{"name": "Demo.src", "file": str(lit)}])
        self.assertEqual(m["result"], "lean-verified-program", m)
        self.f.csrc.write_text("double f(void) { return 2.0; }\n")
        m = self.method(consts, [self.spec(), good_c],
                        literals=[{"name": "Demo.src", "file": str(lit)}])
        self.assertEqual(m["result"], "not-program-verified")


class TestNoticeAndPaths(unittest.TestCase):
    def test_attestations_never_go_to_receipts(self):
        self.assertNotEqual(NA.EVIDENCE.resolve(), NA.RECEIPTS.resolve())
        self.assertIn("Not an IEANTN verification receipt", NA.NOTICE)

    def test_promotion_rule_requires_official_receipt(self):
        self.assertIn("authentic Comparator receipt", SEM["promotion_rule"])


if __name__ == "__main__":
    unittest.main()
