#!/usr/bin/env python3
"""Freshly prove the figure's scalar comparison, without claiming an ANT bridge."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--context", type=Path, required=True)
    parser.add_argument("--run", type=Path, required=True)
    args = parser.parse_args()
    def unique(items):
        result = {}
        for key, value in items:
            need(key not in result, "Duplicate context key")
            result[key] = value
        return result
    context = json.loads(args.context.read_bytes(), object_pairs_hook=unique,
                         parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))
    paths = context["generic_lean_path"]
    if isinstance(paths, str):
        paths = paths.split(":")
    need(isinstance(paths, list) and paths and all(isinstance(x, str) and Path(x).is_dir() for x in paths), "Invalid generic libraries")
    need(not args.run.exists(), "Fresh source-only run required")
    args.run.mkdir(parents=True)
    original = Path(__file__).resolve().parent / "PopulationComparison.lean"
    source = args.run / original.name
    source.write_bytes(original.read_bytes())
    compiler = Path(context["compiler"])
    need(sha(compiler) == context["compiler_sha256"], "Pinned compiler changed")
    version = subprocess.check_output([str(compiler), "--version"], text=True).strip()
    need(version == context["compiler_version"].strip(), "Pinned compiler version changed")
    command = ["/usr/bin/time", "-v", "-o", str(args.run/"run.time"), "prlimit", "--as="+str(32*2**30), "--",
               str(compiler), "-j2", "-R", str(args.run), "-o", str(args.run/"PopulationComparison.olean"), str(source)]
    plan = {"source_sha256":sha(source), "compiler_sha256":sha(compiler), "command":command,
            "context_sha256":sha(args.context), "generic_libraries":paths, "controller_sha256":sha(Path(__file__))}
    (args.run/"PLAN.json").write_text(json.dumps(plan,indent=2)+"\n")
    start = time.monotonic()
    with (args.run/"stdout").open("wb") as out, (args.run/"stderr").open("wb") as err:
        proc = subprocess.run(command,env=dict(os.environ,LEAN_PATH=":".join(paths)),stdout=out,stderr=err)
    need(proc.returncode == 0, "Lean failed; exact snapshot/logs retained")
    output = (args.run/"stdout").read_text()
    for name in ("crossover", "crossover_range", "root_population_octic_shorter"):
        match = re.search("'RH080.PopulationComparison."+name+"' depends on axioms: \\[(.*?)\\]", output)
        need(match is not None, "Missing theorem axiom audit")
        axioms={x.strip() for x in match.group(1).split(",") if x.strip()}
        need(axioms <= {"propext","Classical.choice","Quot.sound"}, "Unaccepted theorem axiom")
    need(sha(original)==sha(source)==plan["source_sha256"], "Source changed during run")
    need(sha(compiler)==plan["compiler_sha256"], "Compiler changed during run")
    result = {"status":"PASS_KERNEL_FORMULA_COMPARISON", "seconds":time.monotonic()-start,
              "source_sha256":sha(source), "object_sha256":sha(args.run/"PopulationComparison.olean"),
              "stdout_sha256":sha(args.run/"stdout"), "stderr_sha256":sha(args.run/"stderr"),
              "plan_sha256":sha(args.run/"PLAN.json"), "source_first_PV":False,
              "scope":"Exact scalar formulas only; actual ANT reductions use separate accepted theorem consumers"}
    need(not (args.run/"RESULT.json").exists(), "Fresh acceptance required")
    temporary=args.run/"RESULT.json.tmp"
    temporary.write_text(json.dumps(result,indent=2)+"\n")
    os.link(temporary,args.run/"RESULT.json");temporary.unlink()
    print(json.dumps({"status":result["status"],"seconds":result["seconds"]}))


if __name__=="__main__":main()
