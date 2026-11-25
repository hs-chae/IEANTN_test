#!/usr/bin/env python3
"""Execute a predeclared V0 or independently eligible V1 wave with preflights.

Mathematical assessment is independent of the mechanical submission gate.
The existing controller and isolated executor are reused without permission changes.
"""
import argparse
import base64
import concurrent.futures
from collections import deque
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time

HERE = Path(__file__).resolve().parent
DATA = Path("/data/ivy-rh-080-20261125")


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    def unique(items):
        result = {}
        for key, value in items:
            need(key not in result, "Duplicate JSON key")
            result[key] = value
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def pin(path):
    return {"path": str(path), "sha256": sha(path)}


def save(path, data):
    path = Path(path)
    need(not path.exists(), "Fresh receipt required: " + str(path))
    temporary = path.with_suffix(path.suffix + ".tmp")
    need(not temporary.exists(), "Stale receipt temporary")
    temporary.write_text(json.dumps(data, indent=2) + "\n")
    os.link(temporary, path)
    temporary.unlink()


def available_ram():
    return 1024 * int(next(l.split()[1] for l in Path("/proc/meminfo").read_text().splitlines()
                           if l.startswith("MemAvailable:")))


def launch(lock, fixture, slot, label):
    directory = lock.parent
    need(available_ram() >= (256 + 64)*2**30, "Preserved host RAM admission reserve unavailable")
    unit = "ivy-rh080-" + label.replace("_", "-").lower()
    command = ["systemd-run", "--user", "--unit=" + unit, "--collect", "--wait", "--pipe",
               "-p", "MemoryMax=64G", "-p", "MemorySwapMax=0", "-p", "CPUQuota=400%"]
    if os.environ.get("CODEX_HOME"):
        # Forward the unchanged active account location, never expose it to the worker.
        command += ["--setenv=CODEX_HOME=" + os.environ["CODEX_HOME"]]
    command += ["--setenv=PATH=" + os.environ["PATH"]]
    cores = list(range(32 + slot*4, 36 + slot*4))
    need(set(cores) <= os.sched_getaffinity(0), "Assigned CPU cores unavailable")
    command += ["/usr/bin/taskset", "-c", ",".join(map(str, cores)),
                "/usr/bin/time", "-v", "-o", str(directory / (label + ".time")),
                sys.executable, str(HERE / "native_trial.py"), "--lock", str(lock)]
    if fixture:
        command.append("--fixture")
    record = {"command": command, "unit": unit, "cpus": cores,
              "available_RAM_at_admission_bytes": available_ram(), "start_unix": time.time(),
              "controller_sha256": sha(HERE / "native_trial.py"),
              "lock_sha256": sha(lock), "fixture": fixture}
    save(directory / (label + ".LAUNCH.json"), record)
    started = time.monotonic()
    with (directory / (label + ".stdout")).open("wb") as stdout, (directory / (label + ".stderr")).open("wb") as stderr:
        p = subprocess.run(command, stdout=stdout, stderr=stderr)
    record.update(returncode=p.returncode, wall_seconds=time.monotonic()-started,
                  stdout_sha256=sha(directory / (label + ".stdout")),
                  stderr_sha256=sha(directory / (label + ".stderr")))
    save(directory / (label + ".EXECUTION.json"), record)
    need(p.returncode == 0, "Trial/fixture process failed; preserved exact output for " + label)
    return record


def accept_fixture(directory, lock_path):
    lock = load(lock_path)
    out = Path(lock["out"])
    result = load(out / "result.json")
    need(result.get("mode") == "NOAUTH_FINAL_CONFIG_FIXTURE", "Not an actual no-auth fixture")
    need(result.get("credentials_mounted_in_worker") is False, "Worker credential boundary failed")
    need(result.get("private_reasoning_collected") is False, "Private reasoning collection enabled")
    need(result.get("mechanical_submission_gate_passed") is True, "Fixture failed export gate")
    need(result.get("stop_reason") is None and result.get("infrastructure_error") is None, "Incomplete fixture")
    need(result.get("artifact_export", {}).get("consistent") is True, "Fixture artifact changed")
    bodies = []
    for item in load(out / "executor/transport.json"):
        if item.get("direction") != "from_executor":
            continue
        message = item.get("message", {})
        params = message.get("params", {})
        if message.get("method") == "process/output" and params.get("stream") == "stdout":
            bodies.append(base64.b64decode(params["chunk"], validate=True))
    probes = []
    for line in b"".join(bodies).splitlines():
        try:
            value = json.loads(line)
        except (ValueError, UnicodeDecodeError):
            continue
        if isinstance(value, dict) and "host_absent" in value:
            probes.append(value)
    need(len(probes) == 1, "Actual worker probe missing or ambiguous")
    probe = probes[0]
    for key in ("host_absent", "controller_canary_absent", "auth_absent", "genericLean_available"):
        need(probe.get(key) is True, "Actual runtime probe failed: " + key)
    need(probe["pid_namespace"] != os.readlink("/proc/self/ns/pid"), "Worker PID namespace not isolated")
    need(probe["net_namespace"] != os.readlink("/proc/self/ns/net"), "Worker network namespace not isolated")
    receipt = {"status": "PASS_EXACT_RH080_ASSIGNED_RUNTIME_AND_NATIVE_ISOLATION",
               "fixture_lock_path": str(lock_path),
               "runtime_sha256": lock["runtime"]["sha256"],
               "packet_manifest_sha256": lock["packet_manifest"]["sha256"],
               "controller_sha256": sha(HERE / "native_trial.py"),
               "backend_result_sha256": sha(out / "result.json"),
               "raw_transport_sha256": sha(out / "executor/transport.json"),
               "actual_worker_probe": probe, "external_model_inference_calls": 0,
               "scope": "Assigned OS/runtime/tool fixture, not mathematical acceptance"}
    path = directory / "PREFLIGHT.json"
    if path.exists():
        need(load(path) == receipt, "Existing preflight no longer matches its actual evidence")
    else:
        save(path, receipt)
    return path


def one(trial, slot, fixture_only, attempt):
    directory = Path(trial["directory"])
    fixture_lock = Path(trial["fixture_lock"])
    if not (directory / "PREFLIGHT.json").exists():
        revised = load(fixture_lock)
        revised["out"] = str(directory / ("fixture-v" + str(attempt)))
        fixture_lock = directory / ("FIXTURE_LOCK_v" + str(attempt) + ".json")
        save(fixture_lock, revised)
        launch(fixture_lock, True, slot, trial["trial"] + "-fixture-v" + str(attempt))
    else:
        fixture_lock = Path(load(directory / "PREFLIGHT.json")["fixture_lock_path"])
    preflight = accept_fixture(directory, fixture_lock)
    if fixture_only:
        return {"trial": trial["trial"], "status": "EXACT_RUNTIME_PREFLIGHT_PASS_NO_RESEARCH"}
    lock = load(fixture_lock)
    protocol = load(HERE / "PROTOCOL.json")
    lock.update(fixture=False, out=str(directory / "research-v1"), preflight=pin(preflight),
                model=protocol["model"]["alias"], effort=protocol["model"]["reasoning_effort"],
                resources=protocol["budgets"], corpus_freeze=pin(HERE / "CORPUS_MANIFEST.json"))
    path = directory / "RESEARCH_LOCK.json"
    save(path, lock)
    launch(path, False, slot, trial["trial"] + "-research")
    result_path = directory / "research-v1/result.json"
    result = load(result_path)
    summary = {"trial": trial["trial"], "result_sha256": sha(result_path),
               "status": "EXECUTED_REQUIRES_INDEPENDENT_MATHEMATICAL_SCORING",
               "mechanical_submission_gate_passed": result.get("mechanical_submission_gate_passed"),
               "stop_reason": result.get("stop_reason"),
               "discovery_admissible_for_evaluation": result.get("discovery_admissible_for_evaluation"),
               "artifact_export": result.get("artifact_export"),
               "no_mathematical_success_inferred_from_gate": True}
    save(directory / "TRIAL_EXECUTION_SUMMARY.json", summary)
    return summary


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--fixture-only", action="store_true")
    parser.add_argument("--wave", choices=("V0", "V1"), default="V0")
    parser.add_argument("--first", type=int, default=16)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--attempt", type=int, default=4)
    a = parser.parse_args()
    bound = 16 if a.wave == "V0" else 4
    need(1 <= a.jobs <= 4 and 1 <= a.first <= bound and a.attempt >= 4, "Predeclared trial/concurrency bound")
    if a.wave == "V1":
        need(load(HERE / "V1_ELIGIBILITY.json")["status"] ==
             "ELIGIBLE_COMPLETED_AND_INDEPENDENTLY_CHECKED_SOURCE_FIRST_CONE", "PV eligibility missing")
    rows = load(HERE / ("PREPARED_" + a.wave + "_RUNTIMES.json"))["trials"][:a.first]
    # Dequeue in frozen order; each live slot retains its distinct four-core set.
    pending = deque(rows)
    gate = threading.Lock()

    def wave(slot):
        results = []
        while True:
            with gate:
                if not pending:
                    break
                trial = pending.popleft()
            results.append(one(trial, slot, a.fixture_only, a.attempt))
        return results

    with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs) as pool:
        result = [entry for group in pool.map(wave, range(a.jobs)) for entry in group]
    save(DATA / (a.wave + ("_FIXTURE_SUMMARY.json" if a.fixture_only else "_EXECUTION_SUMMARY.json")),
         {"status": "COMPLETE_EXECUTION_NOT_MATHEMATICAL_ACCEPTANCE", "trials": result})
    print(json.dumps({"status": "COMPLETE_EXECUTION_NOT_MATHEMATICAL_ACCEPTANCE", "trials": len(result)}))


if __name__ == "__main__":
    main()
