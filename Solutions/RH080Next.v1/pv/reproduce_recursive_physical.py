#!/usr/bin/env python3
"""Compile and physically run the unchanged recursive C ports.

This records compiled observations, not compiler correctness or source PV.
The independent Lean source/model/ANT proof is a separate acceptance route.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
TARGETS = {
    "fap": ("fap_fft_recursive.c", 131072, "781796015790084776\n"),
    "w4": ("w4_fft_recursive.c", 16777216, "7813568381279800\n"),
}
MODES = {
    "O0": ["-O0"], "O2": ["-O2"], "O3": ["-O3"],
    "ubsan": ["-O1", "-fsanitize=undefined", "-fno-sanitize-recover=all"],
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    need(not path.exists(), "Fresh receipt required: " + str(path))
    temp = path.with_name("." + path.name + ".tmp")
    with temp.open("x") as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    try:
        os.link(temp, path)
    finally:
        temp.unlink()


def available_ram():
    values = {line.split(":")[0]: int(line.split()[1])*1024
              for line in Path("/proc/meminfo").read_text().splitlines()}
    return values["MemAvailable"]


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--cc", default="gcc")
    parser.add_argument("--program", choices=["all", *TARGETS], default="all")
    parser.add_argument("--mode", choices=["all", *MODES], default="all")
    parser.add_argument("--memory-gib", type=int, default=64)
    args = parser.parse_args()
    need(1 <= args.memory_gib <= 300, "Per-run memory allowance must be 1..300 GiB")
    need(available_ram() >= (args.memory_gib+256)*2**30,
         "Insufficient available RAM with 256 GiB host reserve")
    if args.memory_gib > 64:
        need(available_ram() >= 2**40, "Above 64 GiB requires genuinely available 1 TiB RAM")
    need(not args.run.exists(), "Fresh run directory required")
    args.run.mkdir(parents=True)
    compiler = Path(shutil.which(args.cc) or args.cc).resolve()
    need(compiler.is_file(), "Compiler unavailable")
    programs = list(TARGETS) if args.program == "all" else [args.program]
    modes = list(MODES) if args.mode == "all" else [args.mode]
    plan = dict(status="PHYSICAL_SOURCE_OBSERVATION_PLAN_NOT_PROOF",
                compiler=str(compiler), compiler_sha256=sha(compiler),
                compiler_version=subprocess.check_output([str(compiler), "--version"], text=True).splitlines()[0],
                controller_sha256=sha(Path(__file__)), python_version=sys.version,
                python_optimize=sys.flags.optimize, available_ram_bytes=available_ram(),
                memory_cap_bytes=args.memory_gib*2**30,
                source_rows=[dict(program=name, source=str(HERE/"fft"/TARGETS[name][0]),
                                  source_sha256=sha(HERE/"fft"/TARGETS[name][0]),
                                  grid=TARGETS[name][1], locked_output=TARGETS[name][2]) for name in programs],
                modes={mode: MODES[mode] for mode in modes},
                assumptions=["precise generic compiler/core runtime/OS/C stdio and hardware contracts",
                             "actual physical execution is associated with the formal model under that boundary"],
                source_first_PV_complete=False, kernel_certificate_complete=False)
    save(args.run/"PLAN.json", plan)
    (args.run/"executed_controller.py").write_bytes(Path(__file__).read_bytes())
    rows = []
    start_all = time.monotonic()
    for source_row in plan["source_rows"]:
        name = source_row["program"]
        source = args.run/TARGETS[name][0]
        source.write_bytes(Path(source_row["source"]).read_bytes())
        need(sha(source) == source_row["source_sha256"], "Source snapshot mismatch")
        for mode in modes:
            stem = name + "-" + mode
            binary = args.run/(stem+".bin")
            command = [str(compiler), "-std=c11", "-Wall", "-Wextra", "-Werror", "-pedantic",
                       *MODES[mode], str(source), "-o", str(binary)]
            t0 = time.monotonic()
            with (args.run/(stem+".compile.stdout")).open("xb") as out, (args.run/(stem+".compile.stderr")).open("xb") as err:
                compiled = subprocess.run(command, stdout=out, stderr=err)
            need(compiled.returncode == 0, "Compilation failed; logs retained: " + stem)
            timing = args.run/(stem+".time")
            execution = ["/usr/bin/time", "-v", "-o", str(timing), "prlimit",
                         "--as="+str(args.memory_gib*2**30), "--stack="+str(256*2**20), "--", str(binary)]
            t1 = time.monotonic()
            with (args.run/(stem+".stdout")).open("xb") as out, (args.run/(stem+".stderr")).open("xb") as err:
                executed = subprocess.run(execution, stdout=out, stderr=err)
            duration = time.monotonic()-t1
            stdout = (args.run/(stem+".stdout")).read_bytes()
            stderr = (args.run/(stem+".stderr")).read_bytes()
            resource = timing.read_text()
            rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", resource)
            row = dict(program=name, mode=mode, compile_command=command, execute_command=execution,
                       source_sha256=sha(source), executable_sha256=sha(binary),
                       compile_seconds=t1-t0, execution_seconds=duration,
                       returncode=executed.returncode, stdout_sha256=sha(args.run/(stem+".stdout")),
                       stderr_sha256=sha(args.run/(stem+".stderr")),
                       peak_rss_kib=int(rss.group(1)) if rss else None,
                       time_sha256=sha(timing), output=stdout.decode("ascii", errors="replace"),
                       oom_event="not_inferred_from_exit_code; inspect enclosing cgroup memory.events",
                       acceptance=False)
            success = executed.returncode == 0 and not stderr and rss is not None and \
                re.fullmatch(rb"[0-9]+\n", stdout) is not None and stdout == TARGETS[name][2].encode("ascii")
            need(sha(Path(source_row["source"])) == sha(source) == source_row["source_sha256"],
                 "Original source changed during physical observation")
            row["acceptance"] = success
            save(args.run/(stem+".RECEIPT.json"), row)
            need(success, "Physical source observation failed; exact failure receipt retained: " + stem)
            rows.append(row)
            print(json.dumps(dict(program=name, mode=mode, execution_seconds=duration,
                                  peak_rss_kib=row["peak_rss_kib"], acceptance=True)), flush=True)
    save(args.run/"RESULT.json", dict(status="PASS_PHYSICAL_SOURCE_OBSERVATIONS_NOT_ALONE_PV",
         plan_sha256=sha(args.run/"PLAN.json"), runs=rows, seconds=time.monotonic()-start_all,
         disk_bytes=sum(p.stat().st_size for p in args.run.rglob("*") if p.is_file()),
         source_first_PV_complete=False, numerical_assumptions_discharged_by_this_script=False))


if __name__ == "__main__":
    main()
