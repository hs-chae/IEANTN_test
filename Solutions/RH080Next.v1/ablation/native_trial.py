#!/usr/bin/env python3
"""New bounded RH study using the existing reviewed isolated executor unchanged.

This adapter changes the mission and explicit packet, not executor permissions.
Corpus/runtime/packet pins and an actual fixture are prerequisites to inference.
"""
import argparse
import asyncio
import hashlib
import importlib.util
import json
import os
from pathlib import Path
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
DATA = Path("/data/ivy-rh080-next-20261125")
BACKEND = Path("/ryu/hyunsik/playground/independence/codex/ivy/ieantn-deep-tertiary-exposure-a-20261117/scripts/native_controller_v2.py")
BACKEND_SHA = "89784de8153c616219a4a93d23f1859845d18924ad472d0d6321fb0eb2661091"


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(2**20), b""):
            h.update(block)
    return h.hexdigest()


def unique(items):
    result = {}
    for key, value in items:
        need(key not in result, "Duplicate JSON key")
        result[key] = value
    return result


def read(path):
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def pin(row):
    need(isinstance(row, dict) and set(row) == {"path", "sha256"}, "Exact file pin required")
    path = Path(row["path"])
    need(path.is_absolute() and path.is_file() and not path.is_symlink(), "Absolute regular input required")
    need(sha(path) == row["sha256"], "Pinned file changed: " + str(path))
    return path


def check_packet(path, expected):
    need(path.is_dir() and not path.is_symlink() and path.resolve().is_relative_to(DATA), "Owned packet required")
    actual = sorted(p.name for p in path.iterdir())
    need(actual == sorted(expected), "Packet population changed")
    for name, value in expected.items():
        need(name == Path(name).name and name not in {".", ".."}, "Flat packet required")
        p = path / name
        need(p.is_file() and not p.is_symlink() and sha(p) == value, "Packet bytes changed")


def check_tree(path, manifest):
    """Read the exact bytes actually mounted, including permitted internal links."""
    path = Path(path)
    data = read(pin(manifest))
    need(Path(data["root"]) == path, "Tree manifest root differs from mount")
    observed = []
    for parent, directories, files in os.walk(path, followlinks=False):
        for name in sorted(directories + files):
            p = Path(parent) / name
            relative = p.relative_to(path).as_posix()
            if p.is_symlink():
                need(p.resolve().is_relative_to(path.resolve()), "Mounted symlink leaves allowed tree")
                observed.append({"path": relative, "symlink": os.readlink(p)})
            elif p.is_file():
                observed.append({"path": relative, "bytes": p.stat().st_size, "sha256": sha(p)})
            else:
                need(p.is_dir(), "Nonregular mounted input")
    need(sorted(observed, key=lambda r: r["path"]) == data["files"], "Actual mounted tree changed")


def import_backend():
    need(sha(BACKEND) == BACKEND_SHA, "Reviewed executor/controller source changed")
    spec = importlib.util.spec_from_file_location("rh080_pinned_native", BACKEND)
    core = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(core)
    return core


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--lock", type=Path, required=True)
    parser.add_argument("--fixture", action="store_true")
    parser.add_argument("--check-only", action="store_true")
    a = parser.parse_args()
    lock = read(a.lock)
    need(lock.get("schema") == "RH080_TRIAL_LOCK_V1" and lock.get("reviewed_by") == "/root", "Reviewed study lock required")
    need(lock.get("fixture") is a.fixture, "Fixture/research lock mismatch")
    protocol = read(pin(lock["protocol"]))
    need(protocol["schema"] == "RH080_PROSPECTIVE_BALANCED_CONTRASTS_V1", "Wrong study protocol")
    need(protocol.get("no_ramanujan") is True, "Excluded target policy missing")
    runtime = read(pin(lock["runtime"]))
    packet_manifest = read(pin(lock["packet_manifest"]))
    packet = Path(packet_manifest["root"])
    check_packet(packet, packet_manifest["files"])
    need(runtime.get("external_network") is False and runtime.get("host_tools") is False, "Runtime boundary changed")
    need(runtime.get("schema") == "RH080_ASSIGNED_RUNTIME_V1", "Wrong runtime")
    need(runtime.get("condition") == lock.get("condition"), "Assigned condition mismatch")
    need(runtime.get("task") == lock.get("task") and runtime.get("replicate") == lock.get("replicate"), "Assigned task mismatch")
    targets = [r["target"] for r in runtime["mounts"]]
    need(len(targets) == len(set(targets)), "Duplicate runtime mount target")
    exact_targets = {"/opt/lean", "/representation", "/source_pv"}
    allowed_prefixes = ("/generic/", "/corpus/", "/representation/", "/source_pv/")
    for row in runtime["mounts"]:
        need(row["target"] in exact_targets or row["target"].startswith(allowed_prefixes), "Unexpected mount target")
        need(Path(row["source"]).is_dir() and not Path(row["source"]).is_symlink(), "Explicit regular mount source required")
        check_tree(Path(row["source"]), row["manifest"])
    if not a.fixture:
        fixture = read(pin(lock["preflight"]))
        need(fixture.get("status") == "PASS_EXACT_RH080_ASSIGNED_RUNTIME_AND_NATIVE_ISOLATION", "Actual fixture prerequisite missing")
        need(fixture.get("runtime_sha256") == sha(lock["runtime"]["path"]), "Fixture belongs to different runtime")
        need(fixture.get("packet_manifest_sha256") == sha(lock["packet_manifest"]["path"]), "Fixture belongs to another packet")
        need(fixture.get("controller_sha256") == sha(__file__), "Fixture belongs to another adapter")
        need(lock.get("model") == protocol["model"]["alias"] and lock.get("effort") == protocol["model"]["reasoning_effort"], "Model setting differs from protocol")
        need(lock["resources"] == protocol["budgets"], "Trial budget differs from preregistration")
        pin(lock["corpus_freeze"])
    out = Path(lock["out"])
    need(out.is_absolute() and out.resolve().is_relative_to(DATA) and not out.exists(), "Fresh owned output required")
    if a.check_only:
        print(json.dumps({"status": "EXACT_LOCK_PACKET_RUNTIME_METADATA_CHECKED_NO_INFERENCE",
                          "fixture": a.fixture, "model_calls": 0}))
        return
    core = import_backend()
    budget = protocol["budgets"]
    args = SimpleNamespace(out=out, packet=packet, model=protocol["model"]["alias"],
        effort=protocol["model"]["reasoning_effort"], fixture=a.fixture,
        wall=budget["active_wall_seconds"], output=budget["output_token_admission"],
        operations=budget["executor_operations"], responses=budget["max_responses"],
        memory_gib=budget["memory_gib"], scratch_gib=budget["scratch_gib"], cpus=budget["cpus"],
        per_response_max_output_tokens=None, phase="RH080_PROSPECTIVE_SCREEN",
        fixture_hook_fault=False, fixture_artifact_name="canary.txt", fixture_boundary_steps=3,
        fixture_draft_at=1, fixture_budget_prefix=False, paired_task_seed=lock.get("replicate", 0),
        compiler=False, python_only=False, environment="", python_optimization=0)
    if not a.fixture:
        core.check_scope({"memory_gib": args.memory_gib, "cpus": args.cpus})
    core.configure_runtime(runtime, args)
    if a.fixture:
        fixture_spec=importlib.util.spec_from_file_location("rh080_new_exposure_fixture", HERE/"proof_fixture.py")
        fixture_module=importlib.util.module_from_spec(fixture_spec);fixture_spec.loader.exec_module(fixture_module)
        core.Fixture=fixture_module.handler(core.Fixture,lock['condition'])
    core.BASE = "You are an independent mathematical research worker in a predeclared offline RH study. Follow only your fresh assigned mission and packet."
    core.DEVELOPER += " Ramanujan is excluded. Keep RH, published analytic source predicates, kernel numerics, and source-first C/C++/CUDA PV distinct. Use no material outside your assigned mounts. Do not claim a proof from a status label or a numeric sample."

    def prompt(directory):
        content = []
        for p in sorted(directory.iterdir()):
            need(p.is_file() and not p.is_symlink(), "Flat regular prompt packet required")
            content.append("\n===== EXACT ASSIGNED FILE /task/" + p.name + " =====\n" + p.read_text())
        return "\n".join(content)

    core.make_prompt = prompt
    asyncio.run(core.main(args))


if __name__ == "__main__":
    main()
