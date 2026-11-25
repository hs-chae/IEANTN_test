#!/usr/bin/env python3
"""Actual normal/-O/-OO registration/replay CLI checks, with source-only fixtures."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

from register_lake import read_json


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--accepted", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repository = here.parents[2]
    need(not args.out.exists(), "Fresh controls directory required")
    accepted = read_json(args.accepted / "RESULT.json")
    current_manifest = read_json(here / "LAKE_PROVIDER_MANIFEST.json")
    project_count = len(current_manifest["solution_projects"])
    need(accepted["status"] == "PASS_ACTUAL_ALL"+str(project_count)+"_REGISTERED_SOLUTION_LAKE_BUILDS" and
         accepted["all_registered_projects_completed"] is True and len(accepted["builds"]) == project_count and
         all(row["returncode"] == 0 for row in accepted["builds"]), "Accepted actual complete registered-project build required")
    args.out.mkdir(parents=True)
    source_manifest = read_json(here / "LAKE_PROVIDER_MANIFEST.json")
    initial = source_manifest["groups"][0]["modules"][0]
    source = repository / source_manifest["groups"][0]["source_root"] / (initial["module"] + ".lean")
    fixtures = {}
    for kind in ["wrong-source", "duplicate-provider", "outside-checkout", "audit-provider"]:
        root = args.out / ("fixture-" + kind)
        entry = root / "Solutions/RH080Study.v1/integration"
        entry.mkdir(parents=True)
        script = entry / "register_lake.py"
        script.write_bytes((here / "register_lake.py").read_bytes())
        data = {"schema": "RH080_LAKE_PROVIDERS_V1", "groups": [{"library": "Fixture",
                "source_root": "providers", "modules": [dict(initial)]}], "solution_projects": []}
        provider = root / "providers" / (initial["module"] + ".lean")
        provider.parent.mkdir()
        provider.write_bytes(source.read_bytes())
        if kind == "wrong-source":
            data["groups"][0]["modules"][0]["sha256"] = "0"*64
            message = "provider changed"
        elif kind == "duplicate-provider":
            data["groups"][0]["modules"].append(dict(initial))
            message = "duplicate module provider"
        elif kind == "outside-checkout":
            data["groups"][0]["source_root"] = "../outside"
            message = "provider outside checkout"
        else:
            data["groups"][0]["modules"][0]["module"] = "FixtureAudit"
            provider.rename(provider.with_name("FixtureAudit.lean"))
            message = "replay-only provider"
        (entry / "LAKE_PROVIDER_MANIFEST.json").write_text(json.dumps(data) + "\n")
        fixtures[kind] = (script, message)
    cases = []

    def run_case(name, command, expected_message=None, expect_success=False):
        proc = subprocess.run(command, cwd=repository, text=True, capture_output=True)
        (args.out / (name + ".stdout")).write_text(proc.stdout)
        (args.out / (name + ".stderr")).write_text(proc.stderr)
        need((proc.returncode == 0) == expect_success, "Unexpected CLI result " + name)
        if expected_message:
            need(expected_message in proc.stderr, "Wrong rejection " + name)
        cases.append({"case": name, "command": command, "returncode": proc.returncode,
                      "expected_acceptance": expect_success,
                      "stdout_sha256": sha(args.out / (name + ".stdout")),
                      "stderr_sha256": sha(args.out / (name + ".stderr"))})
        return proc

    for flags, label in [([], "normal"), (["-O"], "O"), (["-OO"], "OO")]:
        run_case(label + "-registration-positive", [sys.executable, *flags,
                 str(here / "register_lake.py"), "--check"], expect_success=True)
        for key, extra, message in [
            ("existing-output", ["--run", str(args.accepted)], "Fresh run directory required"),
            ("unknown-project", ["--run", str(args.out/(label+"-unknown")), "--projects", "Bogus.v0"], "Unknown/duplicate project"),
            ("duplicate-project", ["--run", str(args.out/(label+"-duplicate")), "--projects", "ThetaCubePopulation.v1", "ThetaCubePopulation.v1"], "Unknown/duplicate project"),
            ("invalid-scheduler", ["--run", str(args.out/(label+"-threads")), "--scheduler-threads", "9"], "invalid choice")]:
            run_case(label + "-" + key, [sys.executable, *flags,
                     str(here / "run_lake_solutions.py"), *extra], expected_message=message)
        for key, (script, message) in fixtures.items():
            run_case(label + "-" + key, [sys.executable, *flags, str(script), "--check"],
                     expected_message=message)
        # This is a genuine cheap selected-project Lake run, not a forged success.
        output = args.out / (label + "-actual-selected-run")
        suffix = hashlib.sha256(str(output.resolve()).encode()).hexdigest()[:10]
        command = ["systemd-run", "--user", "--unit=ivy-rh080-lake-control-" + suffix,
                   "--collect", "--wait", "--pipe", "-p", "MemoryMax=300G", "-p", "MemorySwapMax=0",
                   "-p", "CPUQuota=1600%", "--setenv=PATH=" + os.environ["PATH"],
                   "/usr/bin/taskset", "-c", "48-63", sys.executable, *flags,
                   str(here / "run_lake_solutions.py"), "--run", str(output),
                   "--projects", "ThetaCubePopulation.v1", "--scheduler-threads", "8"]
        run_case(label + "-actual-selected-project", command, expect_success=True)
        result = read_json(output / "RESULT.json")
        need(result["status"] == "PASS_ACTUAL_SELECTED_REGISTERED_SOLUTION_LAKE_BUILDS" and
             result["all_registered_projects_completed"] is False and
             result["projects"] == ["ThetaCubePopulation.v1"] and len(result["builds"]) == 1 and
             result["builds"][0]["returncode"] == 0, "Selected child route claimed wrong coverage")
    for output in args.out.glob("*-unknown"):
        need(not (output / "RESULT.json").exists(), "Rejected child published acceptance")
    need(len(cases) == 30, "Control population differs")
    result = {"status": "PASS30_ACTUAL_LAKE_REGISTRATION_REPLAY_CONTROLS_ALL_OPTIMIZATION_MODES",
              "cases": cases, "source_fixtures_copy_no_objects": True,
              "full_registered_project_acceptance": str(args.accepted / "RESULT.json"),
              "controller_sha256": sha(Path(__file__))}
    temporary = args.out / "RESULT.pending"
    temporary.write_text(json.dumps(result, indent=2) + "\n")
    os.link(temporary, args.out / "RESULT.json")
    temporary.unlink()
    print(json.dumps({"status": result["status"], "cases": len(cases)}))


if __name__ == "__main__":
    main()
