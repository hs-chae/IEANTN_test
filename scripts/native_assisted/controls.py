#!/usr/bin/env python3
"""Lean-level negative and positive controls for the local native-assisted gate.

    python scripts/native_assisted/controls.py [--keep <scratch dir>]

The harness copies `pilots/agentB-calibration` to a scratch directory, never editing the
repository, and adds a `Controls` library of fixture theorems:
* allowed native fact;
* custom axiom;
* fake native-named axiom;
* sorry;
* numeric-only inequality;
* program facts without the correctness theorem;
* a genuine program-linked theorem.

It builds the copy with the real toolchain, extracts each fixture through the real extractor and
applies the real policy. Two mutation controls also run on the copy: a changed executed input
literal and a wrong selected program. Each must make the build fail, and the copy is restored
afterwards. The repository's pilot files are hashed before and after. Results go to
pv-evidence/controls/CONTROLS.json.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import shutil
import subprocess
import sys
import tempfile
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import native_assisted_check as NA  # noqa: E402

PILOT = ROOT / "pilots" / "agentB-calibration"
OUT = ROOT / "pv-evidence" / "controls"

FIXTURES = {
    "Allowed": ("Controls.allowed", "theorem Controls.allowed : (2 : ℕ) ^ 10 = 1024 := by native_decide",
                {"status": "passed", "method": "not-program-verified"}),
    "CustomAxiom": ("Controls.uses_bad",
                    "axiom Controls.bad : (1 : ℕ) = 2\ntheorem Controls.uses_bad : (1 : ℕ) = 2 := Controls.bad",
                    {"status": "failed"}),
    "FakeNative": ("Controls.fake",
                   "axiom Controls.fake._native.native_decide.ax_1_1 : decide ((1 : ℕ) = 2) = true\n"
                   "theorem Controls.fake : (1 : ℕ) = 2 :=\n"
                   "  of_decide_eq_true Controls.fake._native.native_decide.ax_1_1",
                   {"status": "failed"}),
    "Sorry": ("Controls.uses_sorry", "theorem Controls.uses_sorry : (1 : ℕ) = 1 := by sorry",
              {"status": "failed"}),
    "NumericOnly": ("Controls.numeric_only",
                    "theorem Controls.numeric_only :\n    CalibrationPilot.NewA.targets.sum ≤ CalibrationPilot.NewA.bound := by\n  native_decide",
                    {"status": "passed", "method": "not-program-verified"}),
    "NoCorrectness": ("Controls.no_correctness",
                      "theorem Controls.no_correctness :\n    CalibrationPilot.NewA.targets.sum ≤ CalibrationPilot.NewA.bound := by\n"
                      "  have _h := CalibrationPilot.NewA.concrete_execution\n  native_decide",
                      {"status": "passed", "method": "not-program-verified"}),
    "Genuine": ("Controls.genuine",
                "theorem Controls.genuine :\n    ((CalibrationPilot.NewA.targets.sum : ℚ) : ℝ) ≤ (CalibrationPilot.NewA.bound : ℝ) :=\n"
                "  CalibrationPilot.NewA.certified_sum",
                {"status": "passed", "method": "lean-verified-program"}),
}
HEADER = ("/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 "
          "license as described in the file LICENSE.\nAuthors: Agent B (Claude), native-assisted controls\n-/\n")


def tree_hash(d: pathlib.Path) -> str:
    h = hashlib.sha256()
    for p in sorted(d.rglob("*")):
        if p.is_file() and ".lake" not in p.parts:
            h.update(str(p.relative_to(d)).encode()); h.update(p.read_bytes())
    return h.hexdigest()


def bump_first_literal(src: str) -> str:
    """Change the last digit of the first input literal of the executed C source."""
    i = src.index("inputs[7] = {")
    j = src.index("\n", i) + 1
    k = src.index(",", j)
    lit = src[j:k]
    d = lit.rstrip()[-1]
    new = lit.rstrip()[:-1] + str((int(d) + 1) % 10)
    return src[:j] + new + src[k:]


def sh(cmd, cwd, timeout=3600):
    t = time.time()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr, round(time.time() - t, 1)


def main(argv):
    keep = argv[argv.index("--keep") + 1] if "--keep" in argv else None
    before = tree_hash(PILOT)
    scratch = pathlib.Path(keep or tempfile.mkdtemp(prefix="na-controls-"))
    work = scratch / "pilot"
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(PILOT, work, ignore=shutil.ignore_patterns(".lake"))
    lf = (work / "lakefile.toml").read_text()
    lf = lf.replace('path = "../.."', f'path = "{ROOT}"').replace(
        'path = "../../Solutions/RamanujanNumerics.v1"', f'path = "{ROOT}/Solutions/RamanujanNumerics.v1"')
    lf += '\n[[lean_lib]]\nname = "Controls"\n'
    (work / "lakefile.toml").write_text(lf)
    man = json.loads((work / "lake-manifest.json").read_text())
    for pkg in man.get("packages", []):
        if pkg.get("type") == "path" and str(pkg.get("dir", "")).startswith("../.."):
            pkg["dir"] = str(ROOT) + pkg["dir"][len("../.."):]
    (work / "lake-manifest.json").write_text(json.dumps(man, indent=1) + "\n")
    (work / ".lake").mkdir(exist_ok=True)
    (work / ".lake" / "packages").symlink_to(ROOT / ".lake" / "packages")
    (work / "CalibrationPilot.lean").write_text(HEADER + "import CalibrationPilot.NewChain\n")
    (work / "Controls").mkdir()
    imports = []
    for mod, (_, body, _) in FIXTURES.items():
        (work / "Controls" / f"{mod}.lean").write_text(
            HEADER + "import CalibrationPilot.NewA\n\n" + body + "\n")
        imports.append(f"import Controls.{mod}")
    (work / "Controls.lean").write_text(HEADER + "\n".join(imports) + "\n")
    results = {"scratch": str(work), "repository_pilot_tree_sha256_before": before, "fixtures": {},
               "mutations": {}}
    rc, log, secs = sh(["lake", "build", "Controls", "CalibrationPilot"], work, 7200)
    results["build"] = {"rc": rc, "seconds": secs, "tail": log[-1500:]}
    sem = NA.load_json(NA.SEMANTICS)
    src_ok = str(work / "c" / "calibration_new.c")
    for mod, (decl, _, expect) in FIXTURES.items():
        out = work / f"extract_{mod}.json"
        ex, meta = NA.extract(work, "Controls", decl, out)
        if ex is None:
            results["fixtures"][mod] = {"expected": expect, "observed": "extract failed", "ok": False,
                                        "meta": meta}
            continue
        ev = NA.evaluate(ex, None, {"sources": [src_ok]}, sem)
        observed = {"status": ev["status"], "method": ev["method"]["result"],
                    "reasons": ev["reasons"][:3],
                    "native": ev["axioms"]["native_fact_count"],
                    "failed_method_checks": [k for k in ("S_source_identity", "A_source_association",
                        "E_execution_witness", "C_generic_correctness", "M_mathematical_endpoint")
                        if not ev["method"][k]["ok"]]}
        ok = observed["status"] == expect["status"] and observed["method"] == expect.get(
            "method", observed["method"])
        results["fixtures"][mod] = {"endpoint": decl, "expected": expect, "observed": observed, "ok": ok}
        if mod == "Genuine":
            bad = work / "c" / "calibration_new.mismatch.c"
            bad.write_text((work / "c" / "calibration_new.c").read_text().replace("4096.0", "4096.00"))
            ev2 = NA.evaluate(ex, None, {"sources": [str(bad)]}, sem)
            results["fixtures"]["SourceHashMismatch"] = {
                "endpoint": decl, "expected": {"status": "passed", "method": "not-program-verified"},
                "observed": {"status": ev2["status"], "method": ev2["method"]["result"],
                             "S_ok": ev2["method"]["S_source_identity"]["ok"]},
                "ok": ev2["method"]["result"] == "not-program-verified"
                      and not ev2["method"]["S_source_identity"]["ok"]}
    # mutation controls on the scratch copy (build must fail), then restore and rebuild
    muts = {
        "ChangedInputLiteral": (work / "c" / "calibration_new.c", bump_first_literal),
        "WrongSelectedProgram": (work / "CalibrationPilot" / "NewA.lean",
                                 lambda s: s.replace('⟨literals,"4096.0","0.0","0.0"⟩',
                                                     '⟨literals,"2048.0","0.0","0.0"⟩', 1)),
    }
    newa_build = work / ".lake" / "build"

    def force_rebuild_newa():
        # Lake does not trace `include_str` inputs: drop NewA's build products so it recompiles
        for p in newa_build.rglob("NewA.*"):
            p.unlink()

    for name, (path, f) in muts.items():
        orig = path.read_text()
        mutated = f(orig)
        if mutated == orig:
            results["mutations"][name] = {"ok": False, "error": "mutation pattern not found"}
            continue
        path.write_text(mutated)
        rec = {}
        rc0, _, _ = sh(["lake", "build", "CalibrationPilot.NewA"], work, 3600)
        rec["plain_build_rc"] = rc0
        if name == "ChangedInputLiteral":
            # 1) without a forced rebuild the old olean is replayed: the gate must catch the stale
            #    embedded source through S (literal hash != file on disk)
            ex, _ = NA.extract(work, "Controls", "Controls.genuine", work / "extract_stale.json")
            ev = NA.evaluate(ex, None, {"sources": [str(path)]}, sem) if ex else None
            rec["stale_build_replayed"] = rc0 == 0
            rec["gate_detects_stale_source"] = bool(ev) and not ev["method"]["S_source_identity"]["ok"]
        force_rebuild_newa()
        rc, log, secs = sh(["lake", "build", "CalibrationPilot.NewA"], work, 3600)
        first = next((l for l in log.splitlines() if "error" in l), "")
        path.write_text(orig)
        force_rebuild_newa()
        rc2, _, _ = sh(["lake", "build", "CalibrationPilot.NewA"], work, 3600)
        rec.update({"forced_rebuild_rc_mutated": rc, "first_error": first[:300],
                    "build_rc_restored": rc2})
        rec["ok"] = rc != 0 and rc2 == 0 and rec.get("gate_detects_stale_source", True)
        results["mutations"][name] = rec
    results["repository_pilot_tree_sha256_after"] = tree_hash(PILOT)
    results["repository_untouched"] = results["repository_pilot_tree_sha256_after"] == before
    results["all_ok"] = (results["repository_untouched"] and
                         all(v["ok"] for v in results["fixtures"].values()) and
                         all(v["ok"] for v in results["mutations"].values()))
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "CONTROLS.json").write_text(json.dumps(results, indent=1, ensure_ascii=False) + "\n")
    for k, v in {**results["fixtures"], **results["mutations"]}.items():
        print(f"{k:22s} ok={v['ok']}  {v.get('observed', v.get('first_error', ''))}")
    print("repository untouched:", results["repository_untouched"], "| all ok:", results["all_ok"])
    return 0 if results["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
