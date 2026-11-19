from pathlib import Path
import hashlib
import json
import math
import os
import tempfile

ROOT = Path(__file__).resolve().parents[2]
FRONTIERS = ROOT / "coordinator-private/twentyfour-normalized-frontiers-v1"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def pin(path):
    return {"path": str(path), "sha256": sha(path)}


def load(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, "duplicate JSON key")
            result[key] = value
        return result

    def finite(value):
        result = float(value)
        need(math.isfinite(result), "nonfinite JSON number")
        return result

    def reject(value):
        raise ValueError("nonfinite JSON constant: " + value)

    return json.loads(path.read_bytes(), object_pairs_hook=pairs,
                      parse_float=finite, parse_constant=reject)


def fresh_atomic_json(path, value):
    need(not path.exists(), "preserve every earlier accepted receipt")
    fd, temporary = tempfile.mkstemp(prefix="." + path.name + ".", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as stream:
            stream.write(json.dumps(value, indent=2) + "\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)
    finally:
        os.unlink(temporary)


def main():
    prior_closure_path = FRONTIERS / "FINISH_REPRO_R_SCOPE_CLOSURE_AFTER_EXTRACTION_V2.json"
    prior_mapping_path = FRONTIERS / "FINISH_REPRO_R_EXACT_RECEIVER_MAPPING_V2.json"
    current_mapping_path = FRONTIERS / "FINISH_REPRO_R_EXACT_RECEIVER_MAPPING_V3.json"
    paths = [prior_closure_path, prior_mapping_path, current_mapping_path]
    snapshots = [pin(path) for path in paths]
    closure, prior, current = map(load, paths)
    need(closure["exact_checked_mapping"] == pin(prior_mapping_path),
         "the prior completed closure must name the actual preserved prior mapping")
    need(closure["actual_current_function_snapshot"] == prior["current_functions"],
         "the preserved historical snapshot identity must agree")
    finite_path = Path(current["current_functions"]["path"])
    need(pin(finite_path) == current["current_functions"], "fresh actual final numerical snapshot")
    need(pin(Path(current["input_flags"]["path"])) == current["input_flags"],
         "same exact independently read source-scope inputs")
    before = {key: value for key, value in prior.items() if key != "current_functions"}
    after = {key: value for key, value in current.items() if key != "current_functions"}
    need(before == after, "entire R mapping payload changed beyond its final snapshot pin")
    need(not current["unmapped_clauses"] and not current["candidate_additive_source_branches"],
         "no pending scalar clause or required new source branch")
    numeric = current["fixed_receiving_entries"]
    native = current["native_exact_predicates"]
    numeric_keys = [tuple(row["key"]) for row in numeric]
    native_keys = [tuple(key) for row in native for key in row["exact_keys"]]
    need(len(numeric_keys) == len(set(numeric_keys)) == 62, "all62 distinct numeric source keys")
    need(len(native) == 110 and len(native_keys) == len(set(native_keys)) == 135,
         "all110 native predicate groups and135 exact native source keys")
    need(not set(numeric_keys) & set(native_keys), "disjoint numeric and native source keys")
    groups = {row["group"] for row in numeric} | {row["group"] for row in native}
    need(len(groups) == closure["assigned_R_groups"] == 171,
         "all171 independently assigned foundation R groups")
    need(len(set(numeric_keys + native_keys)) == closure["assigned_R_exact_keys"] == 197,
         "all197 exact written-source R keys without collapse")
    need(sum(len(row["parts"]) for row in numeric) == closure["numeric_literal_parts_bound"] == 89,
         "all89 complete literal vectors/domains/cases retain their fresh matching")
    extra = current["extra_Root_assigned_compound_case"]
    need(extra["key"] == ["FOLLOWUP-C022", "OwnD02.old.A-gaps"] and len(extra["parts"]) == 3,
         "allthree separately assigned Root C022 finite/global source parts")
    need(closure["unmapped_scalar_clauses"] == 0, "preserved complete prior source closure")
    for snapshot in snapshots:
        need(sha(Path(snapshot["path"])) == snapshot["sha256"], "input changed during bridge")
    need(pin(finite_path) == current["current_functions"], "final snapshot changed during bridge")
    result = dict(closure)
    result["status"] = "PASS_ALL171_FOUNDATION_R_GROUPS_197_EXACT_KEYS_AND_ROOT_C022_THREE_PARTS_REBOUND_UNCHANGED_TO_FINAL_SNAPSHOT"
    result["actual_current_function_snapshot"] = current["current_functions"]
    result["exact_checked_mapping"] = pin(current_mapping_path)
    result["historical_closure_preserved"] = pin(prior_closure_path)
    result["historical_mapping_preserved"] = pin(prior_mapping_path)
    result["current_snapshot_consistency_bridge"] = {
        "all_mapping_fields_except_current_functions_identical": True,
        "compared_fields": list(before),
        "whole_vectors_domains_cases_source_operators_strictness_native_predicates_and_C022_parts_identical": True,
        "old_snapshot_SHA_is_historical_not_a_current_mutable_path_read": True,
        "final_snapshot_SHA_and_current_mapping_checked_from_actual_bytes": True,
        "current_mapping_freshly_recomputed_with_existing_full_rational_matching_algorithm": True,
        "new_mathematical_reading_or_numerical_scientific_execution": False,
    }
    result["reproduction_sources"] = [pin(Path(__file__)), pin(Path(__file__).with_name(
        "map_foundation_R_receivers_after_literal_extraction_v3_current_snapshot.py"))]
    result["source_first_PV"] = False
    result["full_analytic_Lean"] = False
    output = FRONTIERS / "FINISH_REPRO_R_SCOPE_CLOSURE_AFTER_EXTRACTION_V3.json"
    fresh_atomic_json(output, result)
    print(json.dumps({"closure": pin(output), "final_functions": current["current_functions"],
                      "assigned_R_groups": 171, "assigned_R_exact_keys": 197,
                      "literal_parts": 89, "extra_Root_C022_parts": 3,
                      "unmapped_scalar_clauses": 0}))


if __name__ == "__main__":
    main()
