#!/usr/bin/env python3
"""Seal only the same-source generic-object runtime backfill; no model calls."""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("generic_runtime_comparison", ROOT / "scripts/prepare_main_execution_locks_v2.py")
checks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checks)
need, load, sha, pin, write_new = checks.need, checks.load, checks.sha, checks.pin, checks.write_new
OLD = ROOT / "protocol/runtimes/IEANTN/runtime.json"
NEW_ROOT = ROOT / "protocol/runtimes/IEANTN_GENERIC_COMPLETE_V2"
CACHE_ROOT = ROOT / "resources/ieantn-generic-umbrella-backfill-v1"


def prepare():
    need(sha(OLD) == "e6c339eae26d13efd60e9d233c133c94501f18e2ee53fa6212d47b812dce185b", "original E runtime changed")
    old = load(OLD)
    provenance = CACHE_ROOT / "CACHE_PROVENANCE.json"
    canaries = CACHE_ROOT / "ORDINARY_IMPORT_CANARIES.json"
    result = CACHE_ROOT / "RESULT.json"
    for path in [provenance, canaries, result]:
        need(path.is_file() and isinstance(load(path).get("status"), str) and load(path)["status"].startswith("PASS"),
             "completed actual generic backfill/provenance/ordinary canary receipt required: " + path.name)
    audit_facts = load(provenance)
    need(audit_facts.get("same_mathlib_source_pin") == checks.MATHLIB_SOURCE and
         audit_facts.get("every_existing_permitted_source_hash_unchanged") is True and
         audit_facts.get("compiled_cache_expands_only_existing_exposed_source") is True,
         "generic backfill source identity/closure facts incomplete")
    new = copy.deepcopy(old)
    replaced = []
    for row in new["mounts"]:
        if row["target"].startswith("/evaldeps/"):
            package = row["target"].split("/")[-1]
            manifest = NEW_ROOT / "trees" / ("generic-objects-" + package + ".json")
            need(manifest.is_file(), "new generic object tree manifest missing: " + package)
            tree = load(manifest)
            root = Path(tree["root"])
            need(tree.get("schema") == "DEEP_TERTIARY_TREE_V1" and root.is_dir() and
                 root.is_relative_to(ROOT / "sources/ieantn-generic-umbrella-backfill-v1"),
                 "new object manifest must name the owned same-source official-cache copy")
            need(row["role"] == "generic", "only generic object mounts may be replaced")
            row["source"] = str(root)
            row["manifest"] = pin(manifest)
            replaced.append(row["target"])
    need(len(replaced) == 8, "exact existing eight generic object providers required")
    new["required_imports"] = old["required_imports"] + ["Mathlib", "Mathlib.Tactic"]
    new["preflight_status"] = "VERIFICATION_ONLY_GENERIC_CACHE_BACKFILL_REQUIRES_SIX_EXACT_MAIN_E_PREFLIGHTS"
    original_audit_path = Path(old["native_closure_audit"]["path"])
    need(sha(original_audit_path) == old["native_closure_audit"]["sha256"], "original native closure audit changed")
    audit = load(original_audit_path)
    audit["runtime_mount_manifests"] = [row["manifest"]["sha256"] for row in new["mounts"]]
    audit["verification_only_generic_cache_backfill"] = {
        "old_runtime": pin(OLD), "cache_provenance": pin(provenance), "ordinary_import_canaries": pin(canaries),
        "actual_backfill_result": pin(result), "same_mathlib_source_pin": checks.MATHLIB_SOURCE,
        "every_existing_permitted_source_hash_unchanged": True,
        "compiled_cache_expands_only_existing_exposed_source": True,
        "unchanged_native_source_core_selected_proofs": True, "changed_mount_targets": replaced,
        "no_mathematical_input_or_outcome_changed": True, "source_first_PV_claim": False,
        "runtime_preparation_source": pin(Path(__file__).resolve())}
    audit["remaining_gates"] = "Six actual MAIN IEANTN packet/new-runtime isolation preflights, separate-context DP2 and DP3 compatibility canaries, ROOT verification-only amendment and separate queue start review. No model inference has been performed by this runtime preparation."
    audit_path = NEW_ROOT / "native_closure_audit.json"
    audit_data = checks.encoded(audit)
    new["native_closure_audit"] = {"path": str(audit_path), "sha256": hashlib.sha256(audit_data).hexdigest()}
    return old, new, audit, audit_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    old, new, audit, audit_path = prepare()
    target = NEW_ROOT / "runtime.json"
    if args.write:
        need(not target.exists() and not audit_path.exists(), "fresh additive runtime and audit required")
        write_new(audit_path, audit)
        write_new(target, new)
        audit_path.chmod(0o444)
        target.chmod(0o444)
    if target.exists():
        need(target.read_bytes() == checks.encoded(new) and audit_path.read_bytes() == checks.encoded(audit),
             "existing amended runtime/audit differs from exact regeneration")
        changed = checks.compare_runtimes(old, new)
        print(json.dumps({"status": "PASS_SAME_SOURCE_GENERIC_ONLY_RUNTIME_READBACK_NO_INFERENCE", "runtime": pin(target),
                          "audit": pin(audit_path), "changed_generic_mount_targets": changed}))
    else:
        print(json.dumps({"status": "CHECKED_READY_TO_SEAL_SAME_SOURCE_GENERIC_ONLY_RUNTIME_NO_WRITE_NO_INFERENCE"}))


if __name__ == "__main__":
    main()
