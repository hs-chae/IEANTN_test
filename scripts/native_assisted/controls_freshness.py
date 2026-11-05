#!/usr/bin/env python3
"""Freshness controls for the retrofitted providers (input_file + needs), on scratch copies.

    python scripts/native_assisted/controls_freshness.py [--keep <scratch dir>]

For each retrofitted provider package (RamanujanNumerics.v2, FKS2Numerics.v5), a scratch copy is
made with its path dependencies pointed back at the repository, so the repository is never
edited. Two controls per package, as controls A and B of `controls_pv.py`:

  A  one literal of the selected C file changed, retrofitted lakefile: Lake reruns the input file,
     rebuilds the embedding module, and the certificate fails;
  B  the same change with `needs` removed: Lake replays the stale build (rc 0), and the gate's
     S check (embedded literal hash against the file) is what catches it.

Results: pv-evidence/controls/CONTROLS_FRESHNESS.json. The repository trees are hashed before and
after.
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
OUT = ROOT / "pv-evidence" / "controls"

#: package dir, library to build, C file, literal to bump, the module embedding it
CASES = {
    "RamanujanNumerics.v2": {
        "lib": "Solution",
        "c": "c/updated.c",
        "needs_line": 'needs = ["updated_source", "oldgrouped_source", "updatedgrouped_source"]\n',
    },
    "FKS2Numerics.v5": {
        "lib": "Solution",
        "c": "c/fks2_table4_transport.c",
        "needs_line": 'needs = ["selected_source"]\n',
    },
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


def bump_first_literal(text: str) -> tuple[str, str]:
    """Change the last digit of the first decimal literal inside the first array initializer."""
    m = re.search(r"\{\s*([0-9]+\.[0-9]+)", text)
    lit = m.group(1)
    new = lit[:-1] + str((int(lit[-1]) + 1) % 10)
    return text[:m.start(1)] + new + text[m.end(1):], lit


def scratch_copy(name: str, scratch: pathlib.Path) -> pathlib.Path:
    src = ROOT / "Solutions" / name
    work = scratch / name
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(src, work, ignore=shutil.ignore_patterns(".lake"))
    lf = (work / "lakefile.toml").read_text()
    lf = re.sub(r'path = "\.\./\.\."', f'path = "{ROOT}"', lf)
    lf = re.sub(r'path = "\.\./([^"]+)"', lambda m: f'path = "{ROOT}/Solutions/{m.group(1)}"', lf)
    (work / "lakefile.toml").write_text(lf)
    man_path = work / "lake-manifest.json"
    if man_path.is_file():
        man = json.loads(man_path.read_text())
        for pkg in man.get("packages", []):
            if pkg.get("type") == "path" and not pathlib.Path(pkg.get("dir", "")).is_absolute():
                pkg["dir"] = str((src / pkg["dir"]).resolve())
        man_path.write_text(json.dumps(man, indent=1) + "\n")
    (work / ".lake").mkdir(exist_ok=True)
    (work / ".lake" / "packages").symlink_to(ROOT / ".lake" / "packages")
    return work


def run_case(name: str, case: dict, scratch: pathlib.Path) -> dict:
    work = scratch_copy(name, scratch)
    c_path = work / case["c"]
    lf_path = work / "lakefile.toml"
    orig_c, orig_lf = c_path.read_text(), lf_path.read_text()
    assert case["needs_line"] in orig_lf, f"{name}: retrofitted `needs` line not found"
    rec = {"scratch": str(work)}
    rc, log, secs = sh(["lake", "build", case["lib"]], work, 7200)
    rec["baseline_build"] = {"rc": rc, "seconds": secs, "first_error": first_error(log)}
    mutated, lit = bump_first_literal(orig_c)
    rec["changed_literal"] = lit

    # A: with `needs`, the changed file is rebuilt and the certificate fails
    c_path.write_text(mutated)
    rc, log, secs = sh(["lake", "build", case["lib"]], work, 7200)
    rec["A_with_needs"] = {"rc": rc, "seconds": secs, "first_error": first_error(log),
                           "ok": rc != 0}
    c_path.write_text(orig_c)
    rc2, _, _ = sh(["lake", "build", case["lib"]], work, 7200)
    rec["A_with_needs"]["restored_rc"] = rc2

    # B: without `needs`, Lake replays the stale build
    lf_path.write_text(orig_lf.replace(case["needs_line"], ""))
    rc0, _, _ = sh(["lake", "build", case["lib"]], work, 7200)  # settle without `needs`
    c_path.write_text(mutated)
    rc, log, secs = sh(["lake", "build", case["lib"]], work, 7200)
    rec["B_without_needs"] = {"settle_rc": rc0, "rc": rc, "seconds": secs,
                              "first_error": first_error(log), "ok": rc == 0}
    c_path.write_text(orig_c)
    lf_path.write_text(orig_lf)
    rec["ok"] = (rec["baseline_build"]["rc"] == 0 and rec["A_with_needs"]["ok"]
                 and rec["A_with_needs"]["restored_rc"] == 0 and rec["B_without_needs"]["ok"])
    return rec


def main(argv):
    keep = argv[argv.index("--keep") + 1] if "--keep" in argv else None
    scratch = pathlib.Path(keep or tempfile.mkdtemp(prefix="pv-freshness-"))
    scratch.mkdir(parents=True, exist_ok=True)
    before = {n: tree_hash(ROOT / "Solutions" / n) for n in CASES}
    results = {"scratch": str(scratch), "cases": {}}
    for name, case in CASES.items():
        results["cases"][name] = run_case(name, case, scratch)
    after = {n: tree_hash(ROOT / "Solutions" / n) for n in CASES}
    results["repository_trees_unchanged"] = before == after
    results["all_ok"] = all(c["ok"] for c in results["cases"].values()) and before == after
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "CONTROLS_FRESHNESS.json").write_text(json.dumps(results, indent=1) + "\n")
    print(json.dumps({n: {k: (v.get("ok") if isinstance(v, dict) else v) for k, v in c.items()
                          if k != "scratch"} for n, c in results["cases"].items()}, indent=1))
    print("all_ok", results["all_ok"])
    return 0 if results["all_ok"] else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
