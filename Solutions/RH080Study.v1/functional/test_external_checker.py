#!/usr/bin/env python3
"""Actual normal/-O/-OO CLI controls for the external compact-dual checker."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--run", type=Path, required=True)
    args = ap.parse_args()
    need(not args.run.exists(), "Fresh control directory required")
    args.run.mkdir(parents=True)
    here = Path(__file__).resolve().parent
    source = here / "certify_compact_dual.py"
    fixed = json.loads((here / "COMPACT_DUAL.json").read_text())
    cases = [("valid", fixed, None, None)]
    changes = [
        ("central-height", lambda d: d["positive_heights"].__setitem__(0, 255), "Central steps"),
        ("infeasible-wing", lambda d: d["positive_heights"].__setitem__(4, -582), "exterior step"),
        ("zero-scale", lambda d: d.__setitem__("height_scale", 0), "rational scale"),
        ("short-vector", lambda d: d["positive_heights"].pop(), "height data"),
        ("false-cap", lambda d: d.__setitem__("target_global_bound", "61/50"), "supremum target"),
        ("no-obstruction", lambda d: d.__setitem__("target_global_bound", "13/10"), "four-fifths"),
    ]
    for name, change, reason in changes:
        data = copy.deepcopy(fixed)
        change(data)
        cases.append((name, data, reason, None))
    cases.append(("nonfinite", '{"irrelevant":NaN}', "Nonfinite JSON", None))
    cases.append(("duplicate-key", '{"m":4,"m":4}', "Duplicate JSON", None))
    cases.append(("low-bits", fixed, "Insufficient precision", ["--bits", "80"]))
    cases.append(("zero-panels", fixed, "Insufficient precision", ["--panels", "0"]))
    rows = []
    for flag in (None, "-O", "-OO"):
        mode = flag or "normal"
        for name, data, reason, extra in cases:
            stem = mode.replace("-", "") + "-" + name
            witness = args.run / (stem + ".input.json")
            witness.write_text(data if isinstance(data, str) else json.dumps(data))
            output = args.run / (stem + ".receipt.json")
            command = [sys.executable] + ([flag] if flag else []) + [str(source),
                "--witness", str(witness), "--output", str(output)] + (extra or [])
            result = subprocess.run(command, capture_output=True)
            (args.run / (stem + ".stdout")).write_bytes(result.stdout)
            (args.run / (stem + ".stderr")).write_bytes(result.stderr)
            if reason is None:
                need(result.returncode == 0 and output.is_file(), "Positive CLI did not publish")
                need(json.loads(output.read_text())["accepted_rational_supremum"] == "123/100",
                     "Wrong positive mathematical target")
            else:
                need(result.returncode != 0 and reason.encode() in result.stderr,
                     "Negative did not reach its intended guard: " + stem)
                need(not output.exists() and b'"status"' not in result.stdout,
                     "Rejected CLI published acceptance")
            rows.append(dict(mode=mode, case=name, command=command,
                             returncode=result.returncode, expected_error=reason,
                             stdout_sha256=hashlib.sha256(result.stdout).hexdigest(),
                             stderr_sha256=hashlib.sha256(result.stderr).hexdigest()))
    receipt = dict(status="PASS_33_ACTUAL_EXTERNAL_CHECKER_CLI_CONTROLS",
                   checker_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                   witness_sha256=hashlib.sha256((here/"COMPACT_DUAL.json").read_bytes()).hexdigest(),
                   positives=3, negatives=30, rows=rows,
                   scope="External numerical validator controls only, not the Lean or source-first proof.")
    (args.run / "ACCEPTANCE.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(dict(status=receipt["status"], cases=len(rows))))


if __name__ == "__main__":
    main()
