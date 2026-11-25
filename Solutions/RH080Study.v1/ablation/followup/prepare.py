#!/usr/bin/env python3
"""Freeze the matched numerical-support contrast without changing primary data."""
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


def module_at(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def main():
    helper = module_at("rh080_followup_preparation", HERE.parent / "prepare_runtime_locks.py")
    adapter = module_at("rh080_followup_strict", HERE.parent / "native_trial.py")
    load, save, pin = adapter.read, helper.save, helper.pin
    corpus = HERE.parent / "CORPUS_MANIFEST.json"
    destination = HERE / "CORPUS_MANIFEST.json"
    need(not destination.exists(), "Fresh followup corpus-manifest association required")
    shutil.copyfile(corpus, destination)
    need(sha(corpus) == sha(destination), "Common corpus metadata changed")
    eligibility = load(HERE.parent / "V1_ELIGIBILITY.json")
    need(eligibility["status"] == "ELIGIBLE_COMPLETED_AND_INDEPENDENTLY_CHECKED_SOURCE_FIRST_CONE", "PV not complete")
    cone = load(HERE.parents[1] / "pv/V1_PROOF_CONE_MANIFEST.json")
    all_rows = {x["module"]: x for x in cone["modules"]}
    plan = load(DATA / "pv/fresh-joint-v2-j2/PLAN.json")
    rows = {x["module"]: x for x in plan["modules"]}
    common = set()

    def visit(name):
        if name in common:
            return
        common.add(name)
        for item in rows[name]["imports"]:
            if item in rows:
                visit(item)

    for name in ("CompactDualVerified", "FourierWeakDuality", "FunctionalObstruction"):
        visit(name)
    need(len(common) == 37 and len(all_rows) == 49, "Unexpected frozen support cone")
    need(not {"DualSource", "DualActualRun", "DualVerifiedSource", "CompactDualSourceFirst"} & common,
         "Actual source-first proof leaked into common numerical support")
    need(common <= set(all_rows), "Common support not covered by accepted source-only replay")
    controller = DATA / "ablation-followup-controller"
    support_pins = {}
    for condition, names in (("V0", common), ("V1", set(all_rows))):
        target = DATA / "ablation-followup-support" / condition
        need(not target.exists(), "Fresh support tree required")
        target.mkdir(parents=True)
        for name in sorted(names):
            row = all_rows[name]
            for field, suffix, folder in (("source", ".lean", "source"), ("object", ".olean", "objects")):
                original = Path(row[field])
                need(sha(original) == row[field + "_sha256"], "Accepted provider changed")
                dest = (target / folder).joinpath(*name.split(".")).with_suffix(suffix)
                dest.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(original, dest)
        # The same executable numerical source was common before any PV proof.
        original = HERE.parents[1] / "pv/dual_grid.c"
        shutil.copyfile(original, target / "dual_grid.c")
        save(target / "SUPPORT_MANIFEST.json", {"condition": condition, "modules": sorted(names),
             "common_D_modules": sorted(common), "source_first_modules_added": sorted(names-common),
             "accepted_cone_sha256": sha(HERE.parents[1] / "pv/V1_PROOF_CONE_MANIFEST.json"),
             "numbers_unchanged": True, "new_Gaussian_or_cube_answers": False})
        support_pins[condition] = helper.tree(target, controller / "trees" / (condition + ".json"))
    old_rows = load(HERE.parent / "PREPARED_V0_RUNTIMES.json")["trials"]
    order = load(HERE / "TRIAL_ORDER.json")["trials"]
    prepared = []
    for trial in order:
        condition = trial["computation"]
        old_id = trial["id"].replace("_D1_", "_").replace("_V1-", "_V0-")
        old = next(x for x in old_rows if x["trial"] == old_id)
        old_runtime = load(Path(old["directory"]) / "runtime.json")
        old_packet = load(Path(old["fixture_lock"]))["packet_manifest"]["path"]
        original_packet = Path(load(old_packet)["root"])
        packet = DATA / "ablation-followup-packets" / trial["id"]
        need(not packet.exists(), "Fresh packet required")
        packet.mkdir(parents=True)
        for name in ("COMMON_FACTS.md", "SECONDARY_SOURCE_FACTS.json"):
            shutil.copyfile(original_packet / name, packet / name)
        goal = next(x["goal"] for x in load(HERE / "PROTOCOL.json")["tasks"] if x["id"] == trial["task"])
        (packet / "TASK.md").write_text(
            "# Fresh matched research assignment\n\n" + goal + "\n\n"
            "The same original RH/CMS/Octic sources and the explicit secondary source predicates\n"
            "in SECONDARY_SOURCE_FACTS.json are allowed; disclose any enrichment of assumptions.\n"
            "You have the completed ordinary Lean-kernel compact-dual numerical proof in both\n"
            "arms. Import CompactDualVerified for its L1-Fourier obstruction. It is not a\n"
            "universal impossibility theorem for prime gaps. New Gaussian/cube discoveries\n"
            "made by the coordinator or other trials are not supplied.\n\n"
            + ("V1 additionally exposes the accepted actual-C source-correspondence/execution/main\n"
               "proof, including CompactDualSourceFirst. This establishes the selected scalar-C\n"
               "model's result, under explicit compiler/runtime/ABI/hardware boundaries.\n"
               if condition == "V1" else
               "V0 has kernel numerical support and generic syntax/semantic definitions, but no\n"
               "new theorem connecting the actual C characters and execution to those numbers.\n")
            + "\nPrimary papers: /corpus/literature. Same E2 baseline: /representation.\n"
            "Support sources/objects: /source_pv/source and /source_pv/objects (the path's\n"
            "historical name does not turn ordinary numerical proofs into source-first PV).\n"
            "No Ramanujan work. No outside source/network/other-arm/coordinator context.\n"
            "Budget:1800seconds,36000outputtokens,240executoroperations,128responses,\n"
            "4CPUs,64GiB RAM,12GiB scratch. Preserve exact mathematical statements, assumptions,\n"
            "source/code, proof status, concrete failures and reproducibility commands.\n")
        (packet / "TOOLS_AND_CHECKPOINTS.md").write_text(
            "# Working tools and early checkpoints\n\n"
            "Use /usr/bin/python3.10 for files, directories, hashes, clocks and numerical work.\n"
            "Ordinary ls/cat/date are absent. For example:\n"
            "python3.10 -c 'from pathlib import Path; print([p.name for p in Path(\"/work\").iterdir()])'\n"
            "Read with Path(...).read_text(), enumerate with list(Path(...).iterdir()).\n"
            "Use /bin/lean (bounded wrapper), not the unbounded direct toolchain binary.\n"
            "Support objects already appear on LEAN_PATH; baseline sources are at /representation.\n"
            "Write a valid flat /work/submission early, before spending most of the budget.\n"
            "LOCK.json is a JSON object mapping each other submitted basename to its SHA256.\n"
            "At the neutral25/50/75percent notices, checkpoint partial valid work and honest\n"
            "remaining gaps; do not wait until the final response to create the first LOCK.\n"
            "Later edits require updating all affected hashes before relocking. The finite\n"
            "budget can interrupt a response; a stable earlier locked prefix remains evidence.\n")
        packet_path = controller / "packets" / (trial["id"] + ".json")
        save(packet_path, {"root": str(packet), "files": {p.name: sha(p) for p in sorted(packet.iterdir())}})
        directory = controller / "trials" / trial["id"]
        runtime = dict(old_runtime)
        runtime["condition"] = trial["condition"]
        runtime["mounts"] = old_runtime["mounts"] + [{"role": "source_pv", "target": "/source_pv",
            "source": str(DATA / "ablation-followup-support" / condition), "manifest": support_pins[condition]}]
        runtime["lean_path"] = ["/source_pv/objects"] + old_runtime["lean_path"]
        runtime_path = directory / "runtime.json"
        save(runtime_path, runtime)
        lock = {"schema": "RH080_TRIAL_LOCK_V1", "reviewed_by": "/root", "fixture": True,
                "condition": trial["condition"], "task": trial["task"], "replicate": trial["replicate"],
                "protocol": pin(HERE / "PROTOCOL.json"), "runtime": pin(runtime_path),
                "packet_manifest": pin(packet_path), "out": str(directory / "fixture-v1")}
        lock_path = directory / "FIXTURE_LOCK.json"
        save(lock_path, lock)
        prepared.append({"trial": trial["id"], "directory": str(directory), "fixture_lock": str(lock_path)})
    save(HERE / "PREPARED_RUNTIMES.json", {"status": "PREPARED_MATCHED_FOLLOWUP_BEFORE_INFERENCE",
         "trials": prepared, "common_D_modules": 37, "V1_additional_source_first_modules": 12,
         "protocol_sha256": sha(HERE / "PROTOCOL.json"), "original_results_changed": False})
    print(json.dumps({"status": "PREPARED_MATCHED_FOLLOWUP_BEFORE_INFERENCE", "trials": len(prepared)}))


if __name__ == "__main__":
    main()
