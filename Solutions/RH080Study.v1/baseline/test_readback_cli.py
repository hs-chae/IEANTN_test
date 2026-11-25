#!/usr/bin/env python3
"""Exercise real complete readback and intended rejecting guards in all modes."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


def need(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--scratch", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    a = ap.parse_args()
    need(not a.output.exists(), "Fresh test output required")
    a.output.mkdir(parents=True)
    verifier = Path(__file__).with_name("verify_baseline.py")
    rows = []
    for mode in [[], ["-O"], ["-OO"]]:
        label = mode[0][1:] if mode else "normal"
        positive = a.output / (label + ".json")
        command = [sys.executable] + mode + [str(verifier), "--scratch", str(a.scratch),
                                           "--output", str(positive)]
        p = subprocess.run(command, capture_output=True)
        need(p.returncode == 0 and positive.is_file(), "Actual complete readback failed")
        rows.append(dict(kind="positive", mode=label, command=command, returncode=p.returncode,
                         receipt_sha256=hashlib.sha256(positive.read_bytes()).hexdigest()))
        for kind in ["status", "count", "duplicate"]:
            fixture = a.output / (label + "-" + kind)
            run = fixture / "baseline/frontier300-v1/run"
            run.mkdir(parents=True)
            if kind == "duplicate":
                raw = '{"status":"x","status":"y"}'
                guard = "Duplicate JSON key"
            else:
                raw = json.dumps(dict(
                    status="WRONG" if kind == "status" else
                      "PASS_FRESH_RELOCATED_SOURCE_PROOFS_AND_24_HEADLINE_AUDIT",
                    module_count=299 if kind == "count" else 300))
                guard = "Incomplete actual child acceptance"
            (run / "RESULT.json").write_text(raw)
            receipt = fixture / "ACCEPTANCE.json"
            command = [sys.executable] + mode + [str(verifier), "--scratch", str(fixture),
                                               "--output", str(receipt)]
            p = subprocess.run(command, capture_output=True)
            need(p.returncode != 0 and guard in p.stderr.decode() and not receipt.exists(),
                 "Mutation did not reach its intended rejection guard")
            log = a.output / (label + "-" + kind + ".stderr")
            log.write_bytes(p.stderr)
            rows.append(dict(kind=kind, mode=label, command=command, returncode=p.returncode,
                             guard=guard, guard_observed=True, acceptance_absent=True,
                             stderr_sha256=hashlib.sha256(p.stderr).hexdigest()))
    result = dict(status="PASS_ALL_12_ACTUAL_READBACK_CLI_CASES_NORMAL_O_OO", rows=rows)
    (a.output / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(dict(status=result["status"], cases=len(rows))))


if __name__ == "__main__":
    main()
