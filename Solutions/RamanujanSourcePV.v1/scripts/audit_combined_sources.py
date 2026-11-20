#!/usr/bin/env python3
"""Check every source/object identity in the actual combined analytic/C closure.

This audits existing successful experiment builds; it does not execute missing
proofs, infer theorem acceptance from a file, or claim isolated verification.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json

S = Path(__file__).resolve().parents[1]


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(data)
    return result.hexdigest()


def read(path):
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, "duplicate JSON key: " + key)
            out[key] = value
        return out
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite JSON")))


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--plan", type=Path, required=True)
    parser.add_argument("--legacy-merge", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    need(not args.out.exists(), "fresh audit result required")
    context = read(S / "BUILD_CONTEXT.json")
    bank = Path(context["new_application_object_root"])
    plan = read(args.plan)
    merge = read(args.legacy_merge)
    need(plan["old_application_objects_used"] is False, "source plan forbids old app objects")
    need(merge["status"] == "MERGED_FRESH_QRH_OBJECTS_NO_ROOT_OVERWRITES", "checked fresh merge required")
    need(merge["existing_root_objects_overwritten"] is False, "root preservation")
    need(Path(merge["application_object_root"]) == bank, "actual object prefix")
    fresh_result = Path(merge["fresh_closure"]) / "RESULT.json"
    need(sha(fresh_result) == merge["fresh_result_sha256"], "actual fresh build identity")
    fresh = read(fresh_result)
    need(fresh["status"] == "FRESH_QRH_CLOSURE_BUILD_PASS" and fresh["old_application_objects_used"] is False,
         "actual successful fresh legacy source closure")
    historical = {row["module"]: row for row in merge["rows"]}
    fresh_rows = {row["module"]: row for row in fresh["records"]}
    need(len(historical) == len(merge["rows"]) and len(fresh_rows) == len(fresh["records"]), "unique legacy compiler identities")
    modules = plan["ordered_modules"]
    need(len({m["module"] for m in modules}) == len(modules), "unique planned compiler identities")
    rows = []
    for module in modules:
        name = module["module"]
        source = Path(module["source"])
        need(sha(source) == module["source_sha256"], "planned source drift: " + name)
        obj = bank / Path(*name.split(".")).with_suffix(".olean")
        need(obj.is_file(), "missing actual compiled object: " + name)
        object_hash = sha(obj)
        row = dict(module=name, source=str(source), source_sha256=module["source_sha256"],
                   object_sha256=object_hash)
        if name in historical and object_hash == historical[name]["selected_object_sha256"]:
            prior = historical[name]
            need(prior["source"] == str(source) and prior["source_sha256"] == module["source_sha256"], "legacy source identity: " + name)
            actual = fresh_rows[name]
            need(actual["exit_code"] == 0 and actual["source_sha256"] == module["source_sha256"], "actual fresh compiler success: " + name)
            if prior["selection"] == "RETAINED_ROOT_OBJECT_IDENTICAL_CHECKED_SOURCE":
                receipt = Path(prior["root_receipt"])
                need(sha(receipt) == prior["root_receipt_sha256"], "retained object receipt identity")
                accepted = read(receipt)
                need(accepted["returncode"] == 0 and accepted["object_sha256"] == object_hash, "retained actual object")
                row.update(provenance="SAME_SOURCE_ACCEPTED_ROOT_PROOF", receipt=str(receipt), receipt_sha256=sha(receipt))
            else:
                need(actual["object_sha256"] == object_hash, "fresh compiler object identity: " + name)
                row.update(provenance="ACTUAL_FRESH_LEGACY_BUILD", receipt=str(fresh_result), receipt_sha256=sha(fresh_result))
        else:
            candidates = []
            for receipt in (S / "audit" / name).glob("*/RUN.json"):
                accepted = read(receipt)
                if (accepted.get("status") == "COMPILED" and accepted.get("returncode") == 0
                    and accepted.get("source") == str(source) and accepted.get("source_sha256") == module["source_sha256"]
                    and accepted.get("object_sha256") == object_hash
                    and accepted.get("compiler_sha256") == context["compiler_sha256"]
                    and accepted.get("generic_dependency_context_sha256") == sha(S / "BUILD_CONTEXT.json")):
                    for file, field in [("stdout", "stdout_sha256"), ("stderr", "stderr_sha256"), ("rusage.txt", "rusage_sha256")]:
                        need(sha(receipt.parent / file) == accepted[field], "compiler evidence identity: " + name)
                    if (receipt.parent / "source.lean").exists():
                        need(sha(receipt.parent / "source.lean") == module["source_sha256"], "compiled exact source snapshot: " + name)
                    candidates.append(receipt)
            need(bool(candidates), "no actual current-source/current-object compiler receipt: " + name)
            receipt = sorted(candidates, key=lambda p: int(p.parent.name))[-1]
            row.update(provenance="ACTUAL_NEW_APPLICATION_BUILD", receipt=str(receipt), receipt_sha256=sha(receipt))
        rows.append(row)
    result = dict(schema="ieantn.ramanujan.combined-source-provenance.v1",
                  timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  status="PASS_EVERY_SELECTED_SOURCE_AND_ACTUAL_COMPILED_OBJECT",
                  selected_roots=plan["roots"], module_count=len(rows), rows=rows,
                  plan_sha256=sha(args.plan), legacy_merge_sha256=sha(args.legacy_merge),
                  compiler_sha256=context["compiler_sha256"], old_application_objects_used=False,
                  full_finite_certificate_established=False,
                  scope="Dependency closure of the exact listed roots; not a repository-wide source-claim audit.")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.out.with_name(args.out.name + ".tmp")
    need(not temporary.exists(), "fresh atomic audit temporary")
    temporary.write_text(json.dumps(result, indent=2) + "\n")
    temporary.replace(args.out)
    print(json.dumps({"status": result["status"], "module_count": len(rows), "output": str(args.out), "sha256": sha(args.out)}))


if __name__ == "__main__":
    main()
