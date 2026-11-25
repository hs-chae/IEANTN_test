#!/usr/bin/env python3
"""Execute only the eight separately preregistered, interleaved followup trials."""
import argparse
from collections import deque
import concurrent.futures
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import threading

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--fixture-only", action="store_true")
    parser.add_argument("--check-research-locks-only", action="store_true")
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location("rh080_reused_screen_runner", HERE.parent / "run_screening.py")
    core = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(core)
    core.HERE = HERE
    rows = core.load(HERE / "PREPARED_RUNTIMES.json")["trials"]
    core.need((HERE / "CORPUS_MANIFEST.json").is_file(), "Missing frozen corpus association")
    core.need(core.sha(HERE / "CORPUS_MANIFEST.json") == core.sha(HERE.parent / "CORPUS_MANIFEST.json"),
              "Followup changed the common corpus")
    if not args.fixture_only and not args.check_research_locks_only:
        readiness = core.load(HERE / "ACTUAL_LAUNCH_READINESS.json")
        core.need(readiness.get("status") ==
                  "READY_ALL_EIGHT_RESEARCH_LOCKS_AND_ACTUAL_NAMESPACE_PROOF_TREATMENTS_CHECKED",
                  "Actual treatment/readiness checks are required")
        for row in readiness["checks"]:
            core.need(core.sha(row["path"]) == row["sha256"], "Readiness evidence changed")
    if args.check_research_locks_only:
        checked = []
        for row in rows:
            directory = Path(row["directory"])
            preflight = directory / "PREFLIGHT.json"
            core.need(preflight.is_file(), "Complete every actual fixture before research-lock checks")
            fixture = Path(core.load(preflight)["fixture_lock_path"])
            core.accept_fixture(directory, fixture)
            lock = core.load(fixture)
            protocol = core.load(HERE / "PROTOCOL.json")
            lock.update(fixture=False, out=str(directory / "research-v1"), preflight=core.pin(preflight),
                        model=protocol["model"]["alias"], effort=protocol["model"]["reasoning_effort"],
                        resources=protocol["budgets"], corpus_freeze=core.pin(HERE / "CORPUS_MANIFEST.json"))
            name = "RESEARCH_LOCK_PREFLIGHT_" + str(sys.flags.optimize) + ".json"
            path = directory / name
            core.save(path, lock)
            command = [sys.executable] + (["-" + "O"*sys.flags.optimize] if sys.flags.optimize else [])
            command += [str(HERE / "native_trial.py"), "--lock", str(path), "--check-only"]
            proc = subprocess.run(command, capture_output=True)
            checked.append({"trial":row["trial"],"command":command,"returncode":proc.returncode,
                            "stdout":proc.stdout.decode(),"stderr":proc.stderr.decode()})
            core.need(proc.returncode == 0, "Actual research-lock preflight failed: " + row["trial"])
        core.save(core.DATA / ("FOLLOWUP_RESEARCH_LOCK_PREFLIGHT_"+str(sys.flags.optimize)+".json"),
                  {"status":"PASS_ALL_EIGHT_FULL_RESEARCH_LOCK_CONSTRUCTION_AND_ACTUAL_FRONTDOORS",
                   "model_calls":0,"cases":checked})
        print("Checked all eight complete research locks; no inference")
        return
    pending, lock = deque(rows), threading.Lock()

    def wave(slot):
        results = []
        while True:
            with lock:
                if not pending:
                    return results
                trial = pending.popleft()
            results.append(core.one(trial, slot, args.fixture_only, 4))

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results = [row for group in pool.map(wave, range(4)) for row in group]
    destination = core.DATA / ("FOLLOWUP_FIXTURE_SUMMARY.json" if args.fixture_only else "FOLLOWUP_EXECUTION_SUMMARY.json")
    status = ("ALL_EIGHT_NOAUTH_RUNTIME_FIXTURES_PASS_NO_MODEL_CALLS" if args.fixture_only else
              "SEPARATE_POSTHOC_FOLLOWUP_EXECUTED_NOT_MATHEMATICAL_SCORING")
    core.save(destination, {"status": status,
         "trials": results, "original_results_preserved": True})
    print("All eight no-auth fixtures passed; no model calls" if args.fixture_only else
          "Completed eight separate followup trials; mathematical scoring remains independent")


if __name__ == "__main__":
    main()
