#!/usr/bin/env python3
"""Negative and positive controls for the shared contract and the update workflow.

    python scripts/native_assisted/controls_pv.py [--keep <scratch dir>]

Works on a scratch copy of `Solutions/RamanujanNumerics.v3` (the generated provider), with its
path dependencies pointed back at the repository, so the repository is never edited. Each
mutation is applied to the copy, built with the real toolchain, and restored. Fixture theorems
are extracted with the real extractor and judged by the real gate policy. The repository's v3
tree is hashed before and after. Results: pv-evidence/controls/CONTROLS_PV.json.

Controls:
  A  changed C literal, generated lakefile (input_file + needs): Lake rebuilds, certificate fails
  B  same change with `needs` removed: Lake replays the stale build; the gate's S check catches it
  C  changed literal in the Lean data module only: source mismatch, certificate fails
  D  wrong scale (4097) in both C and Lean: the proved budget is exceeded, certificate fails
  E  first array entry dropped from both C and Lean: the enclosure fails, certificate fails
  F  negative intermediate (offset 300): outside the certified binary64 range, certificate fails
  G  coefficient changed to 118 in data, C and certificate: certificate passes for the changed
     program, but the node statement (coefficient 119) no longer type-checks
  H  certificate replaced by `sorry`: the gate fails (sorryAx)
  I  numeric-only proof of the same statement, no program: gate passes, method not-program-verified
  J  `decide +native` instead of `native_decide`: the gate does not accept the fact
  K  official status after a local pass: designated kind unchanged, no receipt
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import native_assisted_check as NA  # noqa: E402

V3 = ROOT / "Solutions" / "RamanujanNumerics.v3"
OUT = ROOT / "pv-evidence" / "controls"
HEADER = "/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\n" \
         "Released under Apache 2.0 license as described in the file LICENSE.\n" \
         "Authors: Agent B (Claude)\n-/\n"

FIXTURES = {
    "H_Sorry": ("Controls.sorry_budget",
                "import IEANTN.Nodes.RamanujanNumerics.v3.Conclusions\n\n"
                "theorem Controls.sorry_budget : RamanujanNumerics.v3.epsilon_budget := by sorry",
                {"status": "failed"}),
    "I_NumericOnly": ("Controls.numeric_only",
                      "import PVRamanujan.Family\nimport IEANTN.Nodes.RamanujanNumerics.v3.Conclusions\n\n"
                      "open Real in\n"
                      "theorem Controls.numeric_only : RamanujanNumerics.v3.epsilon_budget := by\n"
                      "  intro x hx\n"
                      "  have hlog : (401:ℝ) ≤ log x := by\n"
                      "    have h := log_lt_log (exp_pos _) hx\n    rw [log_exp] at h\n    exact h.le\n"
                      "  have hmaj : DudekPlatt.v3.εUpper (131:ℝ) x - DudekPlatt.v3.εLower (119:ℝ) (exp 400) x ≤\n"
                      "      ForwardRamanujan.upper 119 131 400 401 :=\n"
                      "    ForwardRamanujan.epsilon_majorant (by norm_num) (by norm_num) hlog\n"
                      "  have hq : (PVRamanujan.termsQ 119 131 400 401).sum - 134 - max 0 119 ≤ (2497/250 : ℚ) := by\n"
                      "    native_decide\n"
                      "  have hv : ForwardRamanujan.upper 119 131 400 401 =\n"
                      "      (((PVRamanujan.termsQ 119 131 400 401).sum - 134 - max 0 119 : ℚ) : ℝ) := by\n"
                      "    have := PVRamanujan.termsQ_sum_cast 119 131 400 401\n"
                      "    push_cast at this ⊢\n    rw [ForwardRamanujan.upper, ← this]\n    norm_num\n"
                      "  have hb : (((PVRamanujan.termsQ 119 131 400 401).sum - 134 - max 0 119 : ℚ) : ℝ) ≤\n"
                      "      RamanujanNumerics.v3.allowance := by\n"
                      "    have := (Rat.cast_le (K := ℝ)).2 hq\n"
                      "    norm_num [RamanujanNumerics.v3.allowance] at this ⊢\n    linarith\n"
                      "  linarith",
                      {"status": "passed", "method": "not-program-verified"}),
    "J_DecideNative": ("Controls.decide_native",
                       "import RamanujanBudget.Provider\n\n"
                       "theorem Controls.decide_native :\n"
                       "    PVRamanujan.budgetCheck RamanujanNumerics.v3.Provider.source\n"
                       "      RamanujanNumerics.v3.Provider.program 119 131 400 401 (1 / 10000000000) (2497 / 250) = true := by\n"
                       "  decide +native",
                       {"status": "failed"}),
    "Genuine": ("RamanujanNumerics.v3.Provider.epsilon_budget", None,
                {"status": "passed", "method": "lean-verified-program"}),
}


def tree_hash(d: pathlib.Path) -> str:
    h = hashlib.sha256()
    for p in sorted(d.rglob("*")):
        if p.is_file() and ".lake" not in p.parts:
            h.update(str(p.relative_to(d)).encode())
            h.update(p.read_bytes())
    return h.hexdigest()


def sh(cmd, cwd, timeout=3600):
    t = time.time()
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return p.returncode, p.stdout + p.stderr, round(time.time() - t, 1)


def first_error(log: str) -> str:
    return next((l.strip() for l in log.splitlines() if "error" in l and "trace" not in l), "")[:300]


def bump_digit(text: str, literal: str) -> str:
    """Change the last digit of one literal in a text."""
    assert literal in text, literal
    d = literal[-1]
    return text.replace(literal, literal[:-1] + str((int(d) + 1) % 10), 1)


def main(argv):
    keep = argv[argv.index("--keep") + 1] if "--keep" in argv else None
    before = tree_hash(V3)
    scratch = pathlib.Path(keep or tempfile.mkdtemp(prefix="pv-controls-"))
    work = scratch / "RamanujanNumerics.v3"
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(V3, work, ignore=shutil.ignore_patterns(".lake"))
    lf = (work / "lakefile.toml").read_text()
    lf = lf.replace('path = "../.."', f'path = "{ROOT}"').replace(
        'path = "../ProgramVerification"', f'path = "{ROOT}/Solutions/ProgramVerification"')
    lf += '\n[[lean_lib]]\nname = "Controls"\n'
    (work / "lakefile.toml").write_text(lf)
    man = json.loads((work / "lake-manifest.json").read_text())
    for pkg in man.get("packages", []):
        if pkg.get("type") == "path" and not pathlib.Path(pkg.get("dir", "")).is_absolute():
            pkg["dir"] = str((V3 / pkg["dir"]).resolve())
    (work / "lake-manifest.json").write_text(json.dumps(man, indent=1) + "\n")
    (work / ".lake").mkdir(exist_ok=True)
    (work / ".lake" / "packages").symlink_to(ROOT / ".lake" / "packages")
    (work / "Controls").mkdir()
    imports = []
    for mod, (_, body, _) in FIXTURES.items():
        if body is None:
            continue
        (work / "Controls" / f"{mod}.lean").write_text(HEADER + body + "\n")
        imports.append(f"import Controls.{mod}")
    (work / "Controls.lean").write_text(HEADER + "\n".join(imports) + "\n")

    results = {"scratch": str(work), "repository_v3_tree_sha256_before": before,
               "fixtures": {}, "mutations": {}}
    rc, log, secs = sh(["lake", "build", "Controls", "Solution"], work, 7200)
    results["build"] = {"rc": rc, "seconds": secs, "first_error": first_error(log), "tail": log[-800:]}
    sem = NA.load_json(NA.SEMANTICS)
    src = str(work / "c" / "budget.c")
    for mod, (decl, _, expect) in FIXTURES.items():
        root = "RamanujanBudget" if body_is_none(mod) else "Controls"
        ex, meta = NA.extract(work, root, decl, work / f"extract_{mod}.json")
        if ex is None:
            results["fixtures"][mod] = {"expected": expect, "observed": "extract failed", "ok": False,
                                        "meta": meta}
            continue
        ev = NA.evaluate(ex, None, {"sources": [src]}, sem)
        observed = {"status": ev["status"], "method": ev["method"]["result"],
                    "reasons": ev["reasons"][:3], "native": ev["axioms"]["native_fact_count"]}
        ok = observed["status"] == expect["status"] and observed["method"] == expect.get(
            "method", observed["method"])
        results["fixtures"][mod] = {"endpoint": decl, "expected": expect, "observed": observed, "ok": ok}

    mod_path = work / "RamanujanBudget" / "Provider.lean"
    c_path = work / "c" / "budget.c"
    lit1 = "0.06396484375"  # first array entry, in both files
    orig_c, orig_mod, orig_lf = c_path.read_text(), mod_path.read_text(), (work / "lakefile.toml").read_text()

    def restore():
        c_path.write_text(orig_c)
        mod_path.write_text(orig_mod)
        (work / "lakefile.toml").write_text(orig_lf)

    def build_provider():
        return sh(["lake", "build", "RamanujanBudget"], work, 3600)

    def mutation(name, apply, expect_rc_nonzero=True, extra=None):
        restore()
        apply()
        rc, log, secs = build_provider()
        rec = {"build_rc": rc, "first_error": first_error(log), "seconds": secs,
               "reran_source_input": "Ran selected_source" in log or "selected_source" in log}
        if extra:
            rec.update(extra(rc, log))
        restore()
        rc2, _, _ = build_provider()
        rec["build_rc_restored"] = rc2
        rec["ok"] = ((rc != 0) == expect_rc_nonzero) and rc2 == 0 and rec.get("extra_ok", True)
        results["mutations"][name] = rec

    # A: input_file + needs → a changed C file is rebuilt and the certificate fails
    mutation("A_ChangedC_with_needs", lambda: c_path.write_text(bump_digit(orig_c, lit1)))

    # B: without needs → stale replay; the gate's S check detects the stale embedded source
    def b_apply():
        (work / "lakefile.toml").write_text(orig_lf.replace('needs = ["selected_source"]\n', ""))
        rc0, _, _ = build_provider()  # settle the build without `needs`
        c_path.write_text(bump_digit(orig_c, lit1))

    def b_extra(rc, log):
        ex, _ = NA.extract(work, "RamanujanBudget", "RamanujanNumerics.v3.Provider.epsilon_budget",
                           work / "extract_stale.json")
        ev = NA.evaluate(ex, None, {"sources": [src]}, sem) if ex else None
        detects = bool(ev) and not ev["method"]["S_source_identity"]["ok"]
        return {"stale_build_replayed": rc == 0, "gate_detects_stale_source": detects,
                "extra_ok": rc == 0 and detects}
    mutation("B_ChangedC_without_needs", b_apply, expect_rc_nonzero=False, extra=b_extra)

    # C: changed literal in the Lean data module only
    mutation("C_ChangedLeanLiteral", lambda: mod_path.write_text(bump_digit(orig_mod, lit1)))
    # D: wrong scale in both files
    mutation("D_WrongScale", lambda: (c_path.write_text(orig_c.replace("4096.0", "4097.0")),
                                      mod_path.write_text(orig_mod.replace('"4096.0"', '"4097.0"'))))

    # E: first entry dropped from both files (the program now sums six entries)
    def e_apply():
        c = orig_c.replace(f"    {lit1},\n", "", 1).replace("inputs[7]", "inputs[6]").replace(
            "sum(inputs, 7)", "sum(inputs, 6)")
        m = orig_mod.replace(f'"{lit1}",\n    ', "", 1)
        c_path.write_text(c)
        mod_path.write_text(m)
    mutation("E_DroppedEntry", e_apply)
    # F: negative intermediate (offset 300)
    mutation("F_NegativeIntermediate", lambda: (
        c_path.write_text(orig_c.replace("(r - 134.0)", "(r - 300.0)")),
        mod_path.write_text(orig_mod.replace('"134.0"', '"300.0"'))))

    # G: coefficient 118 everywhere except the node statement
    def g_apply():
        c_path.write_text(orig_c.replace("(r - 119.0)", "(r - 118.0)"))
        mod_path.write_text(orig_mod.replace('"119.0"', '"118.0"').replace(
            "budgetCheck source program 119 131", "budgetCheck source program 118 131"))

    def g_extra(rc, log):
        cert_ok = "certificate" not in first_error(log)
        stmt_fail = "epsilon_budget" in log and rc != 0
        return {"certificate_passed": cert_ok, "statement_rejected": stmt_fail,
                "extra_ok": cert_ok and stmt_fail}
    mutation("G_CoefficientChanged", g_apply, extra=g_extra)

    restore()
    # K: a local pass changes nothing official
    import yaml
    meta = yaml.safe_load((ROOT / "IEANTN/Nodes/RamanujanNumerics/v3/formalization.yaml").read_text())
    conc = meta["conclusions"][0]
    kind = next(j["kind"] for j in conc["justifications"] if j["id"] == conc["designated"])
    receipt = (ROOT / "receipts" / "RamanujanNumerics.v3.epsilon_budget.json").exists()
    att = ROOT / "pv-evidence" / "RamanujanNumerics.v3.epsilon_budget.native-assisted.local.json"
    att_status = json.loads(att.read_text())["status"] if att.is_file() else None
    results["mutations"]["K_OfficialUnchanged"] = {
        "local_gate": att_status, "designated_kind": kind, "receipt_present": receipt,
        "ok": att_status == "passed" and kind == "lean-noncompliant" and not receipt}

    results["repository_v3_tree_sha256_after"] = tree_hash(V3)
    results["repository_untouched"] = results["repository_v3_tree_sha256_after"] == before
    results["all_ok"] = (results["repository_untouched"] and results["build"]["rc"] == 0 and
                         all(v["ok"] for v in results["fixtures"].values()) and
                         all(v["ok"] for v in results["mutations"].values()))
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "CONTROLS_PV.json").write_text(json.dumps(results, indent=1) + "\n")
    for k, v in {**results["fixtures"], **results["mutations"]}.items():
        print(f"{'ok ' if v['ok'] else 'BAD'} {k}")
    print("repository untouched:", results["repository_untouched"], "| all ok:", results["all_ok"])
    return 0 if results["all_ok"] else 1


def body_is_none(mod: str) -> bool:
    return FIXTURES[mod][1] is None


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
