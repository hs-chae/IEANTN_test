#!/usr/bin/env python3
"""Independent receipt/source/object readback for the two completed child runs.

This does not relabel an outer observer termination as a successful observer.
It requires the child frontdoor's actual atomic acceptance, complete compile/audit
receipts and every executed source/object hash. All acceptance checks survive -O.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import tempfile


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pairs(rows):
    output = {}
    for key, value in rows:
        need(key not in output, "Duplicate JSON key")
        output[key] = value
    return output


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def sha(path):
    need(path.is_file() and not path.is_symlink(), "Missing/non-owned evidence file")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--scratch", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    a = ap.parse_args()
    need(not a.output.exists(), "Fresh readback receipt required")
    rows = []
    for name, count, status, auditname in [
        ("frontier300-v1", 300, "PASS_FRESH_RELOCATED_SOURCE_PROOFS_AND_24_HEADLINE_AUDIT", "RESULT.json"),
        ("gaussian53-v1", 53, "PASS_FRESH_RELOCATED_GAUSSIAN_SOURCE_AND_6_HEADLINE_AUDIT", "ACCEPTANCE.json"),
    ]:
        root = a.scratch / "baseline" / name / "run"
        result = read(root / "RESULT.json")
        need(result["status"] == status and result["module_count"] == count,
             "Incomplete actual child acceptance")
        compile_path = root / "compile/EXECUTION.json"
        plan_path = root / "compile/PLAN.json"
        audit_path = root / "audit" / auditname
        need(sha(compile_path) == result["compile_receipt_sha256"], "Compile receipt differs")
        need(sha(audit_path) == result["audit_receipt_sha256"], "Audit receipt differs")
        execution = read(compile_path)
        plan = read(plan_path)
        need(execution["status"] == "PASS_FRESH_TRANSITIVE_COMPILATION",
             "Compilation did not pass")
        need(execution["compiled_modules"] == count == execution["required_modules"],
             "Wrong complete application count")
        need(sha(plan_path) == execution["PLAN_sha256"], "Plan changed")
        built = {row["module"]: row for row in execution["builds"]}
        need(len(built) == len(execution["builds"]) == count, "Duplicate/incomplete build identities")
        need(len(plan["modules"]) == count, "Incomplete executed plan")
        for item in plan["modules"]:
            source = Path(item["executed"])
            object_path = root / "compile/objects" / (item["module"].replace(".", "/") + ".olean")
            need(source.resolve().is_relative_to(root.resolve()), "Executed source outside run")
            need(sha(source) == item["source_sha256"], "Executed source changed")
            need(sha(object_path) == built[item["module"]]["object_sha256"], "Object changed")
        audit = read(audit_path)
        if count == 300:
            need(audit["status"] == "PASS_INDEPENDENT_EXACT_TYPE_AXIOM_VALUE_AUDIT"
                 and audit["headline_count"] == 24 and audit["negative_mathematical_controls"] == 6,
                 "Incomplete frontier consumer audit")
        else:
            need(audit["status"] == "PASS_FRESH_GAUSSIAN_SOURCE_TYPE_VALUE_AXIOM_AND_CONTROLS"
                 and audit["canonical_headliners"] == 6 and len(audit["negative_controls"]) == 6
                 and audit["axiom_value_audit_roots"] == 11 and audit["actual_value_edges"] == 12,
                 "Incomplete Gaussian consumer audit")
        rows.append(dict(packet=name, child_status=result["status"], module_count=count,
                         child_result_sha256=sha(root/"RESULT.json"),
                         compile_receipt_sha256=sha(compile_path), audit_receipt_sha256=sha(audit_path),
                         plan_sha256=sha(plan_path), seconds=result["seconds"], metrics=result["metrics"],
                         all_executed_source_and_object_hashes_verified=True))
    receipt = dict(status="PASS_BOTH_ACTUAL_CHILD_ACCEPTANCES_AND_ALL_353_SOURCE_OBJECT_IDENTITIES",
                   packets=rows, source_first_PV=False,
                   limitation="Readback of actual completed source-only children. The frontier outer-observer exit143 remains separately recorded, not rewritten as zero. Explicit analytic predicates remain assumptions.")
    a.output.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=".baseline-", dir=a.output.parent)
    temporary_path = Path(temporary)
    try:
        with os.fdopen(descriptor, "w") as out:
            json.dump(receipt, out, indent=2); out.write("\n")
            out.flush(); os.fsync(out.fileno())
        os.link(temporary_path, a.output)
    finally:
        temporary_path.unlink()
    print(json.dumps({"status": receipt["status"], "packets": len(rows)}))


if __name__ == "__main__":
    main()
