"""Read existing final metadata evidence; execute no scientific workload."""
from pathlib import Path
import argparse
import ast
import collections
import hashlib
import json
import math
import os
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
F = ROOT / "coordinator-private/twentyfour-normalized-frontiers-v1"
sys.path.insert(0, str(F))
import premises


def need(value, message):
    if not value:
        raise ValueError(message)


def load(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, "duplicate JSON key")
            result[key] = value
        return result

    def finite(value):
        number = float(value)
        need(math.isfinite(number), "JSON number overflow")
        return number

    def reject(value):
        raise ValueError("nonfinite JSON token: " + value)

    return json.loads(path.read_bytes(), object_pairs_hook=pairs,
                      parse_float=finite, parse_constant=reject)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pin(path):
    return {"path": str(path), "sha256": sha(path)}


checked = {}


def verified(ref):
    path = Path(ref["path"])
    if not path.is_absolute():
        path = ROOT / path
    identity = str(path)
    if identity not in checked:
        checked[identity] = sha(path)
    need(checked[identity] == ref["sha256"], "actual source/receipt bytes differ: " + identity)
    return path


def fresh_atomic(path, value):
    need(not path.exists(), "fresh independent receipt required")
    fd, temporary = tempfile.mkstemp(prefix="." + path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as stream:
            stream.write(json.dumps(value, indent=2) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
    finally:
        os.unlink(temporary)


def mode_valid(label, argv):
    mode = label.split("-", 1)[0]
    need(mode in ["normal", "O", "OO"], "known actual optimization mode")
    need(("-O" in argv) == (mode == "O") and ("-OO" in argv) == (mode == "OO"),
         "recorded argv actually uses its claimed optimization mode")


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    names = ["QUANTITATIVE_LITERAL_CLAUSE_COVERAGE.json", "ALL24_SOURCE_BOUND_OBJECTS.json",
             "NORMALIZED_OBJECTS.json", "FINITE_EXPLICIT_FUNCTIONS.json",
             "ACTUAL_ALL24_INTERFACE_NORMAL_O_OO_CONTROLS.json",
             "ACTUAL_PORTABLE_SOURCE_NORMAL_O_OO_READ_DENIAL_CONTROLS.json"]
    snapshots = [pin(F / name) for name in names]
    coverage, source, normalized, finite, controls, portable = [load(F / name) for name in names]
    source_by = {tuple(row["key"]): row for row in source["objects"]}
    norm_by = {tuple(row["key"]): row for row in normalized["objects"]}
    coverage_by = {tuple(row["key"]): row for row in coverage["all11411_rows"]}
    bounds = {row["bound_id"]: row for row in finite["bounds"]}
    need(len(source_by) == len(source["objects"]) == len(norm_by) == len(normalized["objects"])
         == len(coverage_by) == len(coverage["all11411_rows"]) == 11411,
         "all11411 exact identities without collapse")
    need(set(source_by) == set(norm_by) == set(coverage_by), "complete equal source/normal/coverage universe")
    need(len(bounds) == len(finite["bounds"]) == coverage["expanded_function_count"] == 15861,
         "all15861 current unique function identities")
    need(len(source["portfolios"]) == 24, "all24 locked qualified portfolios")
    representation_counts = collections.Counter()
    native_rows = 0
    for key, row in coverage_by.items():
        n, s = norm_by[key], source_by[key]
        identity = {field: s["source"][field] for field in
                    ["file", "sha256", "physical_LF", "physical_LF_end"]}
        need(row["written_identity"] == identity, "whole exact source file/SHA/LF identity")
        verified({"path": identity["file"], "sha256": identity["sha256"]})
        need(row["direct_function_ids"] == n["finite_bound_ids"], "all direct functions preserved")
        for bound_id in row["direct_function_ids"]:
            need(tuple(bounds[bound_id]["object_key"]) == key, "source/function exact-key join")
        evidence = row["actual_source_scope_evidence"]
        if evidence is not None:
            verified(evidence["source"])
        if not row["direct_function_ids"]:
            native_rows += 1
            need(evidence is not None or row["independent_literal_to_function_map"] is not None,
                 "every unexpanded literal has actual independent scope evidence or exact alias")
        verified(row["exact_expression_and_all_domain_parameter_guards"]["normalized_source"])
        need(row["an_unexpanded_scalar_is_not_declared_nonnumerical"] is True,
             "no role/parser-based exclusion proof")
        representation_counts[row["representation_status"]] += 1
    need(dict(representation_counts) == coverage["representation_counts"], "exact representation census")
    function_cases = collections.Counter()
    for bound_id, bound in bounds.items():
        need(bound_id in norm_by[tuple(bound["object_key"])]["finite_bound_ids"],
             "no detached or silently omitted current function")
        case = premises.branch_case(bound)
        function_cases[case] += 1
        need(case in ["B0", "D02"] or (case == "COUNTERFACTUAL_D02" and bound["scope"] == "EXPLICIT_COUNTERFACTUAL_NOT_CURRENT_D01_PREMISE"),
             "every function has a resolved actual case or an explicitly noncurrent counterfactual source case")
    for key, ref in coverage.items():
        if isinstance(ref, dict) and set(ref) >= {"path", "sha256"}:
            verified(ref)
    rclose = load(verified(coverage["independent_R_literal_scope_closure"]))
    mclose = load(verified(coverage["independent_M_literal_scope_closure"]))
    need(rclose["actual_current_function_snapshot"] == snapshots[3], "current R closure snapshot")
    need(rclose["unmapped_scalar_clauses"] == mclose["pending_fixed_numeric_clauses"]
         == coverage["pending_fixed_literal_receiver_clauses"] == 0, "no pending fixed literal clause")
    need(next(ref for ref in mclose["source_snapshots"]
              if Path(ref["path"]).name == "FINITE_EXPLICIT_FUNCTIONS.json") == snapshots[3],
         "current M closure snapshot")
    for ref in mclose["source_snapshots"]:
        verified(ref)
    need(coverage["original2252_source_scope_read_complete"] is True
         and coverage["all_operators_numerically_optimized"] is False,
         "source scope complete while whole-operator optimization is not claimed")
    for ref in controls["input_pins"] + portable["source_pins"]:
        verified(ref)
    verified(controls["source"])
    controller = verified(controls["controller"])
    tree = ast.parse(controller.read_text())
    marker_tables = [ast.literal_eval(node.value) for node in ast.walk(tree)
                     if isinstance(node, ast.Assign) and any(isinstance(target, ast.Name)
                     and target.id == "markers" for target in node.targets)]
    need(len(marker_tables) == 1, "one exact source-defined intended-error table")
    markers = marker_tables[0]
    need(len(controls["records"]) == 72 and len({r["case"] for r in controls["records"]}) == 72,
         "all72 actual unique child routes")
    controls_modes = collections.Counter()
    for record in controls["records"]:
        label, argv = record["case"], record["argv"]
        mode_valid(label, argv)
        mode, case = label.split("-", 1)
        controls_modes[mode] += 1
        stdout = verified(record["stdout"]).read_text()
        stderr = verified(record["stderr"]).read_text()
        if case == "positive":
            need(record["returncode"] == 0 and not stderr, "actual positive child succeeds cleanly")
            positive = load(Path(record["stdout"]["path"]))
            need(positive["objects"] == 11411 and positive["expanded_branches"] == 15861
                 and positive["assertions_used_for_acceptance"] is False, "complete positive metadata check")
        else:
            expected = "REQUIRED_LITERAL_INTERFACE_TABLE_MISSING" if case == "missing-required-literal-table" else markers[case]
            need(record["returncode"] == 1 and "ValueError" in stderr
                 and expected.lower() in stderr.lower(), "actual intended negative route rejection")
    need(controls_modes == {"normal": 24, "O": 24, "OO": 24}, "all24 routes in every optimization mode")
    need(len(portable["records"]) == len({r["label"] for r in portable["records"]}) == 12,
         "all12 actual unique original-workspace-denial routes")
    portable_modes = collections.Counter()
    for record in portable["records"]:
        label = record["label"]
        mode_valid(label, record["argv"])
        mode, operation = label.split("-", 1)
        portable_modes[mode] += 1
        stdout = verified(record["stdout"]).read_text()
        stderr = verified(record["stderr"]).read_text()
        need(record["returncode"] == 0 and not stderr, "actual mapped-source child succeeds cleanly")
        if operation == "deny_probe":
            need(stdout.strip() == "PASS_ACTUAL_ORIGINAL_WORKSPACE_OPEN_DENIAL", "actual deny probe")
        elif operation == "interfaces":
            result = load(Path(record["stdout"]["path"]))
            need(result["objects"] == 11411 and result["expanded_branches"] == 15861,
                 "mapped-only complete current interface check")
        elif operation == "source_collection":
            result = load(Path(record["stdout"]["path"]))
            need(result["objects"] == 11411 and len(result["portfolios"]) == 24,
                 "mapped-only complete source collection")
        else:
            need(operation == "policy" and stdout.strip() == "PASS_EXACT100_SOURCE_BOUND_POLICY_REPRODUCTION",
                 "mapped-only exact assumption-policy reproduction")
    need(portable_modes == {"normal": 4, "O": 4, "OO": 4}, "four original-open-denied routes in every mode")
    verified(portable["public_source_map"])
    verified(portable["materialization"])
    need(portable["source_collection_byteidentical"] is True
         and portable["final_complete_bundle_reconstruction_claimed"] is False,
         "actual source-only portable control is not mislabeled complete final bundle reproduction")
    for ref in snapshots:
        need(sha(Path(ref["path"])) == ref["sha256"], "input changed during independent readback")
    result = {
        "status": "PASS_CURRENT_FINAL24_SOURCE_COVERAGE_CLOSURES_AND_ALL72_PLUS12_ACTUAL_CHILD_RECEIPTS_INDEPENDENTLY_READBACK",
        "source_snapshots": snapshots,
        "validator": pin(Path(__file__)),
        "exact_source_objects": 11411,
        "portfolios": 24,
        "preserved_explicit_functions": 15861,
        "function_cases": dict(function_cases),
        "counterfactual_functions_are_not_current_B0_or_D02_bounds": True,
        "representation_counts": dict(representation_counts),
        "unexpanded_objects_with_actual_scope_or_alias_evidence": native_rows,
        "actual_semantic_controls_verified": 72,
        "actual_original_workspace_denial_controls_verified": 12,
        "actual_source_and_receipt_files_SHA_checked": len(checked),
        "all69_negative_failures_match_the_source_defined_intended_error": True,
        "both_R_and_M_literal_scope_closures_use_final_function_snapshot": True,
        "pending_fixed_literal_clauses": 0,
        "new_mathematical_reading_scientific_execution_or_model_call": False,
        "source_first_PV": False,
        "full_analytic_Lean": False,
        "all_fixed_or_integral_operators_numerically_optimized": False,
        "cleanup_applied": False,
        "verified_paths": [{"path": path, "sha256": digest} for path, digest in sorted(checked.items())],
    }
    fresh_atomic(args.out, result)
    print(json.dumps({"receipt": pin(args.out), "files_SHA_checked": len(checked),
                      "objects": 11411, "functions": 15861, "controls": 84}))


if __name__ == "__main__":
    main()
