#!/usr/bin/env python3
"""Replay the original primal/dual external verifiers and the independent small dual.

Supply the exact original supplement extracted into a fresh private directory.
Its complete source SHA manifest is public; the complete paper/source is not
republished here. This pipeline never substitutes for the Lean or C proofs.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--primary", type=Path, required=True)
    ap.add_argument("--run", type=Path, required=True)
    args = ap.parse_args()
    here = Path(__file__).resolve().parent
    need(not args.run.exists(), "Fresh run directory required")
    source = args.primary.resolve(strict=True)
    pin = json.loads((here / "SOURCE_PIN.json").read_text())
    for row in pin["files"]:
        p = source / row["path"]
        need(p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(source),
             "Missing or unsafe original source")
        need(p.stat().st_size == row["bytes"] and sha(p) == row["sha256"],
             "Pinned primary-source bytes differ: " + row["path"])
    import flint
    need(flint.__version__ == "0.9.0", "python-flint0.9.0 required")
    args.run.mkdir(parents=True)
    certificates = source / "certificates"
    jobs = [
        ("original-dual", [sys.executable, str(certificates/"certify_dual.py"),
            str(certificates/"dual-rh.json"), str(certificates/"dual-grh.json")], 128),
        ("original-primal", [sys.executable, str(certificates/"certify.py")]
            + [str(certificates/n) for n in ["witness-rh.json", "witness-gap.json",
                "witness-grh.json", "witness-grh-m80.json", "witness-ap.json"]]
            + ["--grid-size", "1048576"], 96),
        ("new-reduced-penalty-dual", [sys.executable, str(certificates/"certify_dual.py"),
            str(here/"dual-A5_2-certified-v2.json")], 128),
        ("new-hypothetical-penalty-primal", [sys.executable, str(certificates/"certify.py"),
            str(here/"HYPOTHETICAL_A12_OVER5_PRIMAL.json"), "--grid-size", "1048576"], 96),
        ("new-compact-dual", [sys.executable, str(here/"certify_compact_dual.py"),
            "--witness", str(here/"COMPACT_DUAL.json"),
            "--output", str((args.run/"COMPACT_DUAL_ARB.json").resolve())], 128),
        ("new-checker-controls", [sys.executable, str(here/"test_external_checker.py"),
            "--run", str((args.run/"controls").resolve())], 128),
    ]
    rows = []
    for name, command, bits in jobs:
        metrics = args.run/(name+".time")
        timed = ["/usr/bin/time", "-v", "-o", str(metrics.resolve())] + command
        start = time.monotonic()
        result = subprocess.run(timed, capture_output=True,
            env=dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1"))
        stdout, stderr = args.run/(name+".stdout"), args.run/(name+".stderr")
        stdout.write_bytes(result.stdout)
        stderr.write_bytes(result.stderr)
        need(result.returncode == 0, "External replay failed: " + name)
        rows.append(dict(name=name, command=timed, bits=bits, returncode=result.returncode,
                         seconds=time.monotonic()-start, stdout_sha256=sha(stdout),
                         stderr_sha256=sha(stderr), metrics_sha256=sha(metrics)))
    receipt = dict(status="PASS_EXTERNAL_REPRODUCTION_ONLY_NOT_LEAN_OR_SOURCE_FIRST_PV",
                   primary_pin_sha256=sha(here/"SOURCE_PIN.json"), python=sys.version,
                   python_flint=flint.__version__, jobs=rows,
                   trust="The source verifier's original normal-Python assertions are preserved. The independent new checker has explicit optimization-safe guards. Numerical outputs remain external evidence; the separate Lean/C proof path is audited independently.")
    # Reuse the explicit fresh atomic publisher; all actual child routes have passed.
    from certify_compact_dual import publish
    publish(args.run/"EXTERNAL_REPRODUCTION.json", receipt)
    print(json.dumps(dict(status=receipt["status"], jobs=len(rows))))


if __name__ == "__main__":
    main()
