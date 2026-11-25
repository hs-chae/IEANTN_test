#!/usr/bin/env python3
"""Prepare the exact assigned read-only runtimes and no-auth fixture locks."""
import hashlib
import json
import os
from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = Path("/data/ivy-rh-080-20261125")
R = HERE.parents[2]


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pin(path):
    return {"path": str(path), "sha256": sha(path)}


def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    need(not path.exists(), "Fresh lock/manifest required")
    path.write_text(json.dumps(data, indent=2) + "\n")


def tree(root, destination):
    root = Path(root)
    files = []
    for parent, directories, names in os.walk(root, followlinks=False):
        for name in sorted(directories + names):
            p = Path(parent) / name
            relative = p.relative_to(root).as_posix()
            if p.is_symlink():
                need(p.resolve().is_relative_to(root), "Symlink leaves assigned tree")
                files.append({"path": relative, "symlink": os.readlink(p)})
            elif p.is_file():
                files.append({"path": relative, "bytes": p.stat().st_size, "sha256": sha(p)})
            else:
                need(p.is_dir(), "Nonregular tree entry")
    save(destination, {"root": str(root), "files": sorted(files, key=lambda x: x["path"])})
    return pin(destination)


def main():
    order = json.loads((HERE / "TRIAL_ORDER.json").read_text())
    protocol = json.loads((HERE / "PROTOCOL.json").read_text())
    old = json.loads((R / "Solutions/RHExposureStudy.v1/protocol/runtime-NL_RH.json").read_text())
    controller = DATA / "ablation-controller"
    corpus = json.loads((HERE / "CORPUS_MANIFEST.json").read_text())
    corpus_pin = tree(Path(corpus["root"]), controller / "trees/corpus.json")
    representations = {}
    for kind in ("E0", "E1", "E2"):
        path = DATA / "ablation-representations-v1" / kind
        representations[kind] = tree(path, controller / "trees" / (kind + ".json"))
    prepared = []
    for trial in order["trials"]:
        # V1 may not be instantiated before its whole actual PV path is accepted.
        if trial["computation"] != "V0":
            continue
        name = trial["id"]
        directory = controller / "trials" / name
        mounts = [dict(row) for row in old["mounts"] if row["role"] in ("generic", "toolchain")]
        mounts += [{"role": "literature", "target": "/corpus/literature", "source": corpus["root"],
                    "manifest": corpus_pin},
                   {"role": "representation", "target": "/representation", "source": trial["representation_root"],
                    "manifest": representations[trial["representation"]]}]
        runtime = {"schema": "RH080_ASSIGNED_RUNTIME_V1", "condition": trial["condition"],
                   "task": trial["task"], "replicate": trial["replicate"], "mounts": mounts,
                   "lean_path": old["lean_path"], "external_network": False, "host_tools": False}
        path = directory / "runtime.json"
        save(path, runtime)
        lock = {"schema": "RH080_TRIAL_LOCK_V1", "reviewed_by": "/root", "fixture": True,
                "condition": trial["condition"], "task": trial["task"], "replicate": trial["replicate"],
                "protocol": pin(HERE / "PROTOCOL.json"), "runtime": pin(path),
                "packet_manifest": {"path": trial["packet_manifest"], "sha256": trial["packet_manifest_sha256"]},
                "out": str(directory / "fixture-v1")}
        lp = directory / "FIXTURE_LOCK.json"
        save(lp, lock)
        prepared.append({"trial": name, "fixture_lock": str(lp), "directory": str(directory),
                         "protocol_sha256": sha(HERE / "PROTOCOL.json"),
                         "source_snapshot": sha(HERE / "native_trial.py")})
    save(HERE / "PREPARED_V0_RUNTIMES.json", {"status": "EXACT_MOUNTS_AND_FIXTURE_LOCKS_WRITTEN_NO_INFERENCE",
         "protocol_sha256": sha(HERE / "PROTOCOL.json"), "trials": prepared})
    print(json.dumps({"status": "PREPARED_V0_METADATA_ONLY", "trials": len(prepared), "V1": "INELIGIBLE_UNTIL_COMPLETED_SOURCE_FIRST_PROOF"}))


if __name__ == "__main__":
    main()
