#!/usr/bin/env python3
"""Add the four predeclared V1 runtimes only after independently checked PV."""
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent
DATA = Path("/data/ivy-rh-080-20261125")


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    spec = importlib.util.spec_from_file_location("rh080_runtime_locks", HERE / "prepare_runtime_locks.py")
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    spec = importlib.util.spec_from_file_location("rh080_strict_adapter", HERE / "native_trial.py")
    adapter = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(adapter)
    load, save, pin = adapter.read, helper.save, helper.pin
    study = HERE.parent
    run = DATA / "pv/fresh-joint-v2-j2"
    prerequisites = [
        (run / "RESULT.json", "PASS_FRESH_COMPLETE_SOURCE_FIRST_DUAL_PROGRAM_AND_FULL_MATHEMATICAL_CONSUMER"),
        (DATA / "pv/canonical-append-v1/RESULT.json", "PASS_CANONICAL_SOURCE_FIRST_INTEGRATION_APPEND"),
        (study / "functional/reviews/PV_ACTUAL_C_APPLICATION_COMPONENT_REVIEW.json",
         "PASS_INDEPENDENT_ACTUAL_C_SYNTAX_EXECUTION_AND_APPLICATION_COMPONENT_REVIEW"),
    ]
    for path, status in prerequisites:
        need(load(path).get("status") == status, "PV eligibility prerequisite failed")
    # Copy only the accepted 49-source program cone. No later Gaussian or cube
    # discovery is present in this mount. The primary packets stay byte-identical.
    cone_path = study / "pv/V1_PROOF_CONE_MANIFEST.json"
    cone, result = load(cone_path), load(run / "RESULT.json")
    need(cone["status"] == "EXACT_49_ACCEPTED_PV_PROOF_CONE_FILES_FOR_ADDITIVE_V1_MOUNT", "Unaccepted PV cone")
    need(cone["initial_fresh_run_result_sha256"] == sha(run / "RESULT.json"), "Cone replay differs")
    target = DATA / "ablation-source-pv-v1"
    need(not target.exists(), "Fresh PV mount required")
    target.mkdir()
    rows = []
    for entry in cone["modules"]:
        module = entry["module"]
        source, obj = Path(entry["source"]), Path(entry["object"])
        need(sha(source) == entry["source_sha256"], "Source identity failed")
        need(sha(obj) == entry["object_sha256"], "Accepted object identity failed")
        need("G40" not in module and "G28" not in module and "Cube" not in module, "Unassigned discovery in PV mount")
        for folder, path in (("source", source), ("objects", obj)):
            suffix = ".lean" if folder == "source" else ".olean"
            destination = target / folder / Path(*module.split(".")).with_suffix(suffix)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, destination)
            need(sha(destination) == sha(path), "Mount copy mismatch")
        rows.append({"module": module, "source_sha256": sha(source), "object_sha256": sha(obj)})
    c_source = study / "pv/dual_grid.c"
    need(sha(c_source) == result["actual_C_source_sha256"], "Actual C bytes changed")
    shutil.copyfile(c_source, target / "dual_grid.c")
    (target / "README.md").write_text(
        "# Accepted source-first proof support\n\n"
        "Actual C: dual_grid.c. The matching Lean sources are in source/ and freshly\n"
        "compiled accepted proof objects in objects/. Add /source_pv/objects to\n"
        "LEAN_PATH. The compiler and generic Mathlib are identical to the other arms.\n"
        "Import CompactDualSourceFirst for the source-linked mathematical result.\n"
        "Its real Fourier-pair hypotheses include L1 of both functions; this is a\n"
        "restricted functional obstruction, not an impossibility theorem for prime gaps.\n"
        "The pure C function returns 1221161. Successful formatting yields its\n"
        "decimal bytes followed by newline. main returning zero alone does not\n"
        "guarantee successful physical stdout; libc/OS/hardware and the selected\n"
        "scalar-C semantic contract remain explicit trusted infrastructure.\n"
        "No new Gaussian or cube discovery is supplied here.\n")
    save(target / "ACCEPTED_CONE.json", {"modules": rows, "prerequisites": [pin(p) for p, _ in prerequisites],
         "actual_C_source_sha256": sha(c_source), "numerical_values_changed": False,
         "formal_proof_availability_is_an_additional_primary_contrast": True})
    controller = DATA / "ablation-controller"
    tree_pin = helper.tree(target, controller / "trees/source-pv-v1.json")
    order = load(HERE / "TRIAL_ORDER.json")
    previous = load(HERE / "PREPARED_V0_RUNTIMES.json")["trials"]
    prepared = []
    for trial in order["trials"]:
        if trial["computation"] != "V1":
            continue
        directory = controller / "trials" / trial["id"]
        # Same E2 representation and common papers as its paired primary V0.
        old_id = trial["id"].replace("_V1-", "_V0-")
        old = next(x for x in previous if x["trial"] == old_id)
        runtime = load(Path(old["directory"]) / "runtime.json")
        runtime["condition"] = trial["condition"]
        runtime["mounts"].append({"role": "source_pv", "target": "/source_pv",
                                  "source": str(target), "manifest": tree_pin})
        runtime["lean_path"] = ["/source_pv/objects"] + runtime["lean_path"]
        path = directory / "runtime.json"
        save(path, runtime)
        lock = {"schema": "RH080_TRIAL_LOCK_V1", "reviewed_by": "/root", "fixture": True,
                "condition": trial["condition"], "task": trial["task"], "replicate": trial["replicate"],
                "protocol": pin(HERE / "PROTOCOL.json"), "runtime": pin(path),
                "packet_manifest": {"path": trial["packet_manifest"], "sha256": trial["packet_manifest_sha256"]},
                "out": str(directory / "fixture-v1")}
        need(sha(trial["packet_manifest"]) == trial["packet_manifest_sha256"], "Original packet changed")
        fixture = directory / "FIXTURE_LOCK.json"
        save(fixture, lock)
        prepared.append({"trial": trial["id"], "directory": str(directory), "fixture_lock": str(fixture),
                         "protocol_sha256": sha(HERE / "PROTOCOL.json"), "source_snapshot": sha(HERE / "native_trial.py")})
    save(HERE / "V1_ELIGIBILITY.json", {"status": "ELIGIBLE_COMPLETED_AND_INDEPENDENTLY_CHECKED_SOURCE_FIRST_CONE",
         "prerequisites": [pin(p) for p, _ in prerequisites], "accepted_cone": pin(cone_path), "mount": tree_pin,
         "time_wave_confound": True,
         "proof_availability_confound": "Primary V1 adds completed formal numerical and source proofs; primary V0 has identical values plus external checking. No isolated causal PV effect is claimed.",
         "new_Gaussian_or_cube_discoveries_mounted": False,
         "original_packets_unchanged": True})
    save(HERE / "PREPARED_V1_RUNTIMES.json", {"status": "PREPARED_FOUR_PREDECLARED_V1_NO_INFERENCE",
         "eligibility_sha256": sha(HERE / "V1_ELIGIBILITY.json"), "trials": prepared})
    print(json.dumps({"status": "PREPARED_FOUR_PREDECLARED_V1_NO_INFERENCE", "sources": len(rows)}))


if __name__ == "__main__":
    main()
