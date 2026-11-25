#!/usr/bin/env python3
"""Associate observed Lake/core/check evidence with final public configuration.

This is local study bookkeeping, not an official Comparator or proof receipt.
Historical handoffs and official receipt bytes are never rewritten.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path

from register_lake import expected_files, read_json


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--phase", type=Path, required=True)
    parser.add_argument("--lake-run", type=Path, required=True)
    parser.add_argument("--controls", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    need(not args.out.exists(), "Fresh integration addendum required")
    here = Path(__file__).resolve().parent
    repository = here.parents[2]
    study = here.parent
    manifest = read_json(here / "LAKE_PROVIDER_MANIFEST.json")
    project_count = len(manifest["solution_projects"])
    outputs = expected_files(repository, manifest)
    for path, text in outputs.items():
        need(path.read_text() == text, "Registration differs: " + str(path))
    lake = read_json(args.lake_run / "RESULT.json")
    plan = read_json(args.lake_run / "PLAN.json")
    need(lake["status"] == "PASS_ACTUAL_ALL"+str(project_count)+"_REGISTERED_SOLUTION_LAKE_BUILDS" and
         lake["all_registered_projects_completed"] is True and
         len(lake["builds"]) == project_count and
         set(lake["projects"]) == set(manifest["solution_projects"]), "Incomplete actual registered-project build")
    need(lake["plan_sha256"] == sha(args.lake_run / "PLAN.json"), "Lake plan changed")
    need(lake["controller_sha256"] == sha(here / "run_lake_solutions.py") and
         plan["source_registration_sha256"] == sha(here / "LAKE_PROVIDER_MANIFEST.json") and
         plan["registrar_sha256"] == sha(here / "register_lake.py"), "Frozen controller/configuration differs")
    for relative, expected in plan["files"].items():
        need(sha(repository / relative) == expected, "Build input changed: " + relative)
    for row in lake["builds"]:
        name = row["project"]
        need(row["returncode"] == 0 and row["resource_failure"] is None, "Failed actual project")
        for suffix, key in [("stdout", "stdout_sha256"), ("stderr", "stderr_sha256"), ("time", "time_sha256")]:
            need(sha(args.lake_run / (name + "." + suffix)) == row[key], "Actual project log changed")
        need("Exit status: 0" in (args.lake_run / (name + ".time")).read_text(), "Actual GNU success absent")
    core_path = args.phase / "core-final-v1"
    core = read_json(core_path / "RESULT.json")
    core_plan = read_json(core_path / "PLAN.json")
    need(core["status"] == "PASS_GENUINE_LAKE_CORE_HASH_FINGERPRINT" and
         core["completed"] == core["core_modules"] == len(core_plan["modules"]) and
         all(row["returncode"] == 0 for row in core["builds"] + core["subsequent"]), "Core/hash/fingerprint failed")
    for row in core_plan["modules"]:
        need(sha(Path(row["file"])) == row["source_sha256"], "Current core source differs")
    proof_path = args.phase / "proof-audit-normal" / "RESULT.json"
    proof = read_json(proof_path)
    need(proof["status"] == "PASS_ACTUAL_LAKE_SOLUTION_TYPES_VALUES_AND_STD3_TRANSITIVE_AXIOMS" and
         proof["project_count"] == project_count and proof["projects"] == manifest["solution_projects"] and
         proof["source_registration_sha256"] == sha(here / "LAKE_PROVIDER_MANIFEST.json") and
         proof["lake_result_sha256"] == sha(args.lake_run / "RESULT.json"), "Actual current Solution proof audit incomplete")
    need(proof["producer_sha256"] == sha(here / "final-integration-v2/audit_lake_solutions.py") and
         len(proof["rows"]) == project_count and
         {row["project"] for row in proof["rows"]} == set(manifest["solution_projects"]), "Proof audit producer/population differs")
    for row in proof["rows"]:
        need(row["returncode"] == 0 and all(set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}
             for axioms in row["theorem_axioms"].values()), "Nonstandard actual Solution proof axiom")
        need(sha(repository / row["object_path"]) == row["object_sha256"], "Audited Solution object changed")
        project = repository / "Solutions" / row["project"]
        config = read_json(project / "comparator.json")
        need(sha(project / "comparator.json") == row["comparator_sha256"] and
             sha(project / "Solution.lean") == row["solution_source_sha256"] and
             set(config["theorem_names"]) == set(row["theorem_axioms"]), "Audited Solution root identities differ")
        audit_directory = proof_path.parent / row["project"]
        for name, key in [("stdout", "stdout_sha256"), ("stderr", "stderr_sha256"),
                          ("run.time", "time_sha256"), ("ProofAudit.lean", "audit_source_sha256")]:
            need(sha(audit_directory / name) == row[key], "Actual proof audit artifact changed")
        audit_output = (audit_directory / "stdout").read_text()
        for name in config["theorem_names"]:
            match = re.search("'"+re.escape(name)+"' depends on axioms: \\[(.*?)\\]", audit_output, re.S)
            need(match is not None and {item.strip() for item in match.group(1).split(",") if item.strip()} ==
                 set(row["theorem_axioms"][name]), "Actual proof stdout differs from axiom receipt")
    controls = read_json(args.controls / "RESULT.json")
    need(controls["status"] == "PASS30_ACTUAL_LAKE_REGISTRATION_REPLAY_CONTROLS_ALL_OPTIMIZATION_MODES" and
         len(controls["cases"]) == 30, "Actual optimization controls incomplete")
    gates = read_json(args.phase / "FINAL_STRUCTURAL_GATES.json")
    required_gates = {"graph-current", "fingerprints-current", "check-current"}
    need({row["name"] for row in gates["commands"]} == required_gates, "Structural gate population differs")
    for row in gates["commands"]:
        need(row["returncode"] == (1 if row["name"] == "check-current" else 0), "Unexpected structural gate result")
        for suffix in ["stdout", "stderr"]:
            need(sha(args.phase / (row["name"]+"."+suffix)) == row[suffix+"_sha256"], "Structural gate log changed")
    for relative, expected in gates["current_node_metadata_sha256"].items():
        need(sha(repository / relative) == expected, "Node metadata changed after current graph audit")
    comparison = read_json(args.phase / "INHERITED_CHECK_COMPARISON.json")
    need(comparison["status"] == "EXPECTED_INHERITED_FAILURE_EXACT49_NORMALIZED_ERRORS_AND_RECEIPT_BYTES_UNCHANGED" and
         comparison["baseline_error_count"] == comparison["current_error_count"] == 49 and
         comparison["normalized_baseline_errors"] == comparison["normalized_current_errors"] and
         comparison["full_check_PASS_claimed"] is False, "Repository check comparison changed")
    derived_errors = []
    section = None
    for line in (args.phase / "check-current.stdout").read_text().splitlines():
        if line.startswith("FAIL "):
            section = line[5:]
        elif line.startswith(("ok ", "warn ", "PASS ")):
            section = None
        elif section and line.startswith("  - "):
            derived_errors.append([section, re.sub(r", not `[^`]+`$", ", not `<CHECKOUT_REPOSITORY_IDENTITY>`", line[4:])])
    need(sorted(derived_errors) == comparison["normalized_current_errors"] and
         sha(args.phase / "check-current.stdout") == comparison["current_stdout_sha256"],
         "Actual current error log differs from inherited comparison")
    for row in comparison["affected_receipts"]:
        need(sha(repository / row["path"]) == row["current_sha256"], "Inherited receipt changed")
    deltas = []
    validator_deltas = []
    report_helper_deltas = []
    historical = []
    portability_path = study / "CONTROL_PORTABILITY_ADDENDUM.json"
    portability = read_json(portability_path)
    need(portability["status"] == "PASS_ADDITIVE_G80_G56_CONTROL_PORTABILITY_REPAIR" and
         len(portability["changes"]) == 2, "Reviewed portability addendum differs")
    portability_pairs = {}
    for row in portability["changes"]:
        need(row["family"] in ["G80", "G56"] and row["original_mathematical_claims_and_results_changed"] is False and
             sha(repository / row["current_validator"]) == row["current_validator_sha256"] and
             sha(repository / row["historical_validator_snapshot"]) == row["historical_validator_sha256"] and
             sha(repository / row["current_control_receipt"]) == row["control_result_sha256"],
             "Reviewed portability source/history/control association differs")
        portability_pairs[row["current_validator"]] = row
    need(len(portability_pairs) == 2, "Duplicate reviewed portability validator")

    def visit(value, owner):
        if isinstance(value, dict):
            filename = value.get("path", value.get("file"))
            expected = value.get("sha256", value.get("source_sha256"))
            if isinstance(filename, str) and isinstance(expected, str) and len(expected) == 64:
                path = Path(filename)
                if not path.is_absolute():
                    path = repository / path
                if path.is_relative_to(repository) and path.is_file() and sha(path) != expected:
                    relative = path.relative_to(repository)
                    if (str(relative) == str((study / "reports/check_report_browser.py").relative_to(repository)) and
                            owner.is_relative_to(study / "reviews/final-report-reader")):
                        report_helper_deltas.append({"historical_handoff": str(owner.relative_to(repository)),
                            "path": str(relative), "historical_sha256": expected, "current_sha256": sha(path),
                            "classification": "Concurrent owner report-reader validator; outside mathematical/Lake integration scope, recorded without claiming report acceptance"})
                    elif str(relative) in portability_pairs:
                        reviewed = portability_pairs[str(relative)]
                        need(expected == reviewed["historical_validator_sha256"] and
                             sha(path) == reviewed["current_validator_sha256"],
                             "Historical validator change does not match the exact reviewed portability pair")
                        validator_deltas.append({"historical_handoff": str(owner.relative_to(repository)),
                            "path": str(relative), "historical_sha256": expected, "current_sha256": sha(path),
                            "control_receipt": reviewed["current_control_receipt"],
                            "classification": "Previously reviewed validation-only portability repair; numerical producer/claims/accepted mathematics unchanged"})
                    else:
                        need(path.name in ["lakefile.toml", "lake-manifest.json", "formalization.yaml", "README.md"],
                             "Non-packaging historical source changed: " + str(relative))
                        deltas.append({"historical_handoff": str(owner.relative_to(repository)),
                                       "path": str(relative), "historical_sha256": expected,
                                       "current_sha256": sha(path), "classification": "Packaging/source metadata only; mathematical Lean unchanged"})
            for child in value.values():
                visit(child, owner)
        elif isinstance(value, list):
            for child in value:
                visit(child, owner)

    for path in sorted(study.rglob("*HANDOFF*.json")):
        if "integration" in path.relative_to(study).parts:
            continue
        historical.append({"path": str(path.relative_to(repository)), "sha256": sha(path)})
        visit(read_json(path), path)
    configs = [{"path": str(path.relative_to(repository)), "sha256": sha(path), "bytes": path.stat().st_size}
               for path in sorted(outputs)]
    result = {"status": "PASS_FINAL_ORDINARY_LAKE_CORE_GRAPH_AND_CONFIGURATION_ASSOCIATION_WITH_EXPLICIT_INHERITED_CHECK_FAILURE",
              "scope": "Local incremental packaging/current-core bookkeeping; not source-cold mathematical proof replay, official Comparator approval or whole-project completion",
              "projects": lake["projects"], "provider_groups": len(manifest["groups"]),
              "providers": sum(len(group["modules"]) for group in manifest["groups"]),
              "configuration_outputs": configs, "historical_handoffs_read_only": historical,
              "historical_metadata_hash_deltas": deltas, "historical_validator_hash_deltas": validator_deltas,
              "historical_report_helper_deltas_outside_math_scope": report_helper_deltas, "report_acceptance_claimed": False,
              "reviewed_portability_addendum_sha256": sha(portability_path), "mathematical_Lean_source_hash_deltas": 0,
              "actual_Lake_result": {"path": str(args.lake_run / "RESULT.json"), "sha256": sha(args.lake_run / "RESULT.json")},
              "actual_core_result": {"path": str(core_path / "RESULT.json"), "sha256": sha(core_path / "RESULT.json"), "modules": core["core_modules"]},
              "actual_proof_audit": {"path": str(proof_path), "sha256": sha(proof_path), "theorems": proof["theorem_count"]},
              "actual_controls": {"path": str(args.controls / "RESULT.json"), "sha256": sha(args.controls / "RESULT.json"), "cases": 30},
              "repository_check": {"actual_status": "FAIL49_INHERITED_RECEIPT_REPOSITORY_IDENTITY_ERRORS", "comparison_sha256": sha(args.phase / "INHERITED_CHECK_COMPARISON.json"), "receipt_bytes_unchanged_against_two_ancestors": True},
              "source_registration_sha256": sha(here / "LAKE_PROVIDER_MANIFEST.json"),
              "producer_sha256": sha(Path(__file__)), "current_structural_gates_sha256": sha(args.phase / "FINAL_STRUCTURAL_GATES.json"),
              "official_Comparator_approval": False}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.out.with_suffix(args.out.suffix + ".pending")
    with temporary.open("x") as stream:
        json.dump(result, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.link(temporary, args.out)
    temporary.unlink()
    print(json.dumps({"status": result["status"], "projects": len(result["projects"]),
                      "metadata_deltas": len(deltas), "configurations": len(configs)}))


if __name__ == "__main__":
    main()
