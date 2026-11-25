#!/usr/bin/env python3
"""Fresh complete source-first dual program and mathematical consumer replay.

Only pinned generic Lean/Mathlib package objects are reused. All selected C/source
syntax, execution, sine, Fourier-dual and final application proofs are snapshotted
and compiled afresh. The memory-intensive complete C-AST execution is serialized.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(p):
    need(p.is_file() and not p.is_symlink(), "Expected regular owned file: " + str(p))
    return hashlib.sha256(p.read_bytes()).hexdigest()


def pairs(items):
    result = {}
    for k, v in items:
        need(k not in result, "Duplicate JSON key")
        result[k] = v
    return result


def read(p):
    return json.loads(p.read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def atomic(p, data):
    need(not p.exists(), "Fresh receipt required: " + str(p))
    fd, name = tempfile.mkstemp(prefix=".receipt-", dir=p.parent)
    q = Path(name)
    try:
        with os.fdopen(fd, "w") as f:
            json.dump(data, f, indent=2); f.write("\n"); f.flush(); os.fsync(f.fileno())
        os.link(q, p)
    finally:
        q.unlink()


def memory_available():
    return int(next(l.split()[1] for l in Path("/proc/meminfo").read_text().splitlines()
                    if l.startswith("MemAvailable:"))) * 1024


def generic(context, repository):
    compiler = Path(context["compiler"]).resolve(strict=True)
    need(sha(compiler) == context["compiler_sha256"], "Compiler bytes differ")
    version = subprocess.check_output([str(compiler), "--version"], text=True).strip()
    need("4.34.0-rc2" in version, "Wrong Lean version")
    manifest = read(repository / "Solutions/RHOnePrimeEvolution.v1/gaussian_gap/portable/SOURCE_MANIFEST.json")
    pins = {r["name"]: r["revision"] for r in manifest["generic_dependencies"]}
    paths = context["generic_lean_path"].split(":")
    need(len(paths) == 8 and len(set(paths)) == 8 and all(paths), "Exactly eight explicit generic libraries required")
    seen = set()
    rows = []
    for name in paths:
        p = Path(name)
        need(p.is_absolute() and p.is_dir() and p.parts[-4:] == (".lake", "build", "lib", "lean"),
             "Generic library layout differs")
        package = p.parents[3]
        need(package.name in pins and package.name != "Cli" and package.name not in seen,
             "Unpinned/duplicate/application provider")
        need("/.lake/packages/" in str(package), "Expected pinned package layout")
        revision = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(package), "status", "--porcelain", "--untracked-files=no"], text=True)
        need(revision == pins[package.name] and not dirty, "Generic pin/tracked source differs")
        seen.add(package.name)
        rows.append(dict(name=package.name, revision=revision, library=str(p)))
    return compiler, paths, rows


def sources(repository):
    study = repository / "Solutions/RH080Study.v1"
    table = {}
    for base in [study/"pv/lean", study/"sine", study/"functional",
                 repository/"Solutions/RHOnePrimeEvolution.v1/gaussian_gap/portable/source"]:
        for p in base.rglob("*.lean"):
            module = str(p.relative_to(base)).removesuffix(".lean").replace("/", ".")
            if module in table:
                need(table[module].read_bytes() == p.read_bytes(), "Ambiguous source module " + module)
            else:
                table[module] = p
    generic_prefixes = ("Mathlib", "Lean", "Init", "Std", "Aesop", "Batteries", "Qq", "ProofWidgets")
    done, active, order = set(), set(), []
    def visit(module):
        if module in done:
            return
        if module not in table:
            need(any(module == x or module.startswith(x+".") for x in generic_prefixes),
                 "Missing application source " + module)
            return
        need(module not in active, "Application import cycle")
        active.add(module)
        p = table[module]
        imports = []
        for line in p.read_text().splitlines():
            if line.startswith("import "):
                imports.extend(line[7:].split("--", 1)[0].split())
        for dependency in imports:
            visit(dependency)
        active.remove(module); done.add(module)
        order.append(dict(module=module, origin=str(p), source_sha256=sha(p), imports=imports))
    visit("PVJointAudit")
    return order


def time_fields(p):
    result = {}
    for line in p.read_text().splitlines():
        s = line.strip()
        for prefix, key in [("User time (seconds):", "user_seconds"),
                            ("System time (seconds):", "system_seconds"),
                            ("Maximum resident set size (kbytes):", "peak_process_RSS_KiB")]:
            if s.startswith(prefix):
                value = s[len(prefix):].strip()
                result[key] = int(value) if key.endswith("KiB") else float(value)
    return result


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--repository", type=Path, required=True)
    ap.add_argument("--context", type=Path, required=True)
    ap.add_argument("--run", type=Path)
    ap.add_argument("--check-only", action="store_true")
    a = ap.parse_args()
    repository = a.repository.resolve(strict=True)
    context = read(a.context)
    compiler, libraries, generic_rows = generic(context, repository)
    order = sources(repository)
    need(any(r["module"] == "DualActualRun" for r in order), "Actual C execution omitted")
    need(any(r["module"] == "CompactDualSourceFirst" for r in order), "Final mathematical consumer omitted")
    if a.check_only:
        print(json.dumps(dict(status="PASS_SOURCE_AND_GENERIC_PREFLIGHT_ONLY", sources=len(order),
                              actual_C_execution_included=True, final_math_consumer_included=True)))
        return
    need(a.run is not None and not a.run.exists(), "Fresh --run required")
    run = a.run.resolve(); run.mkdir(parents=True)
    source = run/"source"; objects = run/"objects"; logs = run/"logs"
    for p in [source, objects, logs]:
        p.mkdir()
    began = time.monotonic()
    controller_hash = sha(Path(__file__))
    (run/"reproduce_joint.executed.py").write_bytes(Path(__file__).read_bytes())
    study = repository/"Solutions/RH080Study.v1"
    program = study/"pv/dual_grid.c"
    source_inputs = [program, study/"pv/PARAMETERS.json", study/"pv/parse_source.py"]
    for row in order:
        target = source/(row["module"].replace(".", "/")+".lean")
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(Path(row["origin"]).read_bytes())
        row["executed"] = str(target)
    generator = run/"source-generator"; generator.mkdir(); (generator/"lean").mkdir()
    for p in source_inputs:
        shutil.copyfile(p, generator/p.name)
    generator_command = [sys.executable, str(generator/"parse_source.py")]
    generated = subprocess.run(generator_command, capture_output=True)
    (logs/"generator.stdout").write_bytes(generated.stdout); (logs/"generator.stderr").write_bytes(generated.stderr)
    need(generated.returncode == 0, "Actual source frontend regeneration failed")
    for name in ["DualAST.lean", "DualSource.lean"]:
        need((generator/"lean"/name).read_bytes() == (source/name).read_bytes(),
             "Source/AST regeneration differs: " + name)
    # Check every physical ASCII source byte against the formal character list.
    import re
    source_text = (source/"DualSource.lean").read_text()
    char_section = source_text.split("def sourceChars : List Char := [", 1)[1].split("]", 1)[0]
    represented = bytes(int(n) for n in re.findall(r"Char.ofNat ([0-9]+)", char_section))
    need(represented == (generator/"dual_grid.c").read_bytes(), "Actual C/formal source byte association differs")
    inputs = [dict(origin=str(p), copied=str(generator/p.name), sha256=sha(generator/p.name)) for p in source_inputs]
    atomic(run/"PLAN.json", dict(status="FROZEN_PLAN_NOT_ACCEPTANCE", modules=order,
        roots=["PVJointAudit"], compiler=str(compiler), compiler_sha256=sha(compiler),
        generic=generic_rows, predecessor_application_objects_used=False,
        per_normal_process_AS_bytes=64*2**30, heavy_execution_AS_bytes=256*2**30,
        host_RAM_reserve_bytes=256*2**30, heavy_serialized=True, source_inputs=inputs,
        generator_command=generator_command, exact_C_source_characters_match=True,
        startup_available_RAM_bytes=memory_available(), startup_free_disk_bytes=shutil.disk_usage(run).free,
        controller_sha256=controller_hash))
    env = dict(os.environ, LEAN_PATH=str(objects)+":"+":".join(libraries))
    builds = []
    for row in order:
        cap = (256 if row["module"] == "DualActualRun" else 64)*2**30
        need(memory_available() > 256*2**30+cap, "Host reserve admission failed before compiler launch")
        module = row["module"]
        target = objects/(module.replace(".", "/")+".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        stem = module.replace(".", "_")
        out, err, timing = logs/(stem+".stdout"), logs/(stem+".stderr"), logs/(stem+".time")
        command = ["/usr/bin/time", "-v", "-o", str(timing), "prlimit", "--as="+str(cap), "--",
                   str(compiler), "-j2", "-R", str(source), "-o", str(target), row["executed"]]
        start = time.monotonic()
        with out.open("wb") as o, err.open("wb") as e:
            result = subprocess.run(command, cwd=source, env=env, stdout=o, stderr=e)
        item = dict(module=module, command=command, returncode=result.returncode,
                    seconds=time.monotonic()-start, source_sha256=sha(Path(row["executed"])),
                    stdout_sha256=sha(out), stderr_sha256=sha(err), time_sha256=sha(timing),
                    metrics=time_fields(timing), AS_cap_bytes=cap)
        if result.returncode != 0:
            atomic(run/"FAILED.json", dict(status="FAILED_FRESH_SOURCE_BUILD", builds=builds+[item]))
            raise ValueError("Fresh compilation failed: " + module)
        item["object_sha256"] = sha(target); builds.append(item)
        progress = run/"PROGRESS.json"
        temporary = run/".progress.json"
        temporary.write_text(json.dumps(dict(finished=len(builds), total=len(order), latest=module))+"\n")
        os.replace(temporary, progress)
    audit = logs/"PVJointAudit.stdout"
    need("PV_JOINT_AUDIT_PASS roots=13 edges=11 no-native no-sorry no-D-cap-shortcut" in audit.read_text(),
         "Missing actual complete proof/value/axiom audit")
    native = run/"native"; native.mkdir()
    native_source = native/"dual_grid.c"; native_source.write_bytes((generator/"dual_grid.c").read_bytes())
    executable = native/"dual_grid"
    cc = shutil.which("cc"); need(cc is not None, "C compiler unavailable")
    cc_hash = sha(Path(cc).resolve())
    c_command = [cc, "-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-pedantic",
                 str(native_source), "-o", str(executable)]
    c = subprocess.run(c_command, capture_output=True)
    (native/"compile.stdout").write_bytes(c.stdout); (native/"compile.stderr").write_bytes(c.stderr)
    need(c.returncode == 0, "Actual C source compilation failed")
    executed = subprocess.run([str(executable)], capture_output=True)
    (native/"stdout").write_bytes(executed.stdout); (native/"stderr").write_bytes(executed.stderr)
    need(executed.returncode == 0 and executed.stdout == b"1221161\n" and not executed.stderr,
         "Actual stdout differs from kernel-proved serialization")
    for row, build in zip(order, builds):
        need(sha(Path(row["executed"])) == row["source_sha256"] == sha(Path(row["origin"])),
             "Source association changed during execution")
        need(sha(objects/(row["module"].replace(".", "/")+".olean")) == build["object_sha256"],
             "Accepted object changed")
    for item in inputs:
        need(sha(Path(item["origin"])) == item["sha256"] == sha(Path(item["copied"])),
             "C/source-generator input changed")
    need(sha(Path(__file__)) == controller_hash == sha(run/"reproduce_joint.executed.py"),
         "Executed controller association changed")
    need(sha(compiler) == context["compiler_sha256"], "Lean compiler changed")
    need(sha(Path(cc).resolve()) == cc_hash, "C compiler changed during execution")
    result = dict(status="PASS_FRESH_COMPLETE_SOURCE_FIRST_DUAL_PROGRAM_AND_FULL_MATHEMATICAL_CONSUMER",
                  seconds=time.monotonic()-began, modules=len(order), builds=builds,
                  PLAN_sha256=sha(run/"PLAN.json"), actual_C_source_sha256=sha(native_source),
                  C_compiler=cc, C_compiler_sha256=cc_hash,
                  C_compiler_version=subprocess.check_output([cc, "--version"], text=True).splitlines()[0],
                  C_compile_command=c_command, C_compile_returncode=c.returncode,
                  executable_sha256=sha(executable), execution_command=[str(executable)],
                  execution_returncode=executed.returncode, stdout_sha256=sha(native/"stdout"),
                  stdout_hex=executed.stdout.hex(), audit_stdout_sha256=sha(audit),
                  observed_SIGKILL_compiler_events=sum(r["returncode"] == -9 for r in builds),
                  peak_individual_process_RSS_KiB=max(r["metrics"].get("peak_process_RSS_KiB",0) for r in builds),
                  user_CPU_seconds=sum(r["metrics"].get("user_seconds",0) for r in builds),
                  system_CPU_seconds=sum(r["metrics"].get("system_seconds",0) for r in builds),
                  final_owned_allocated_disk_bytes=int(subprocess.check_output(["du","-sB1",str(run)],text=True).split()[0]),
                  predecessor_application_objects_used=False, source_first_PV=True,
                  limitations="Fixed-input scalar C program and L1 Fourier-functional obstruction; not a prime-gap lower bound or unrestricted optimizer. Actual main/format logic is proved; successful I/O/capture is explicit, never a generic platform success assumption. Generic pinned libraries/compiler/C ABI/libc/OS/hardware remain trust boundaries. GNU per-process RSS is not aggregate host peak; final disk is not measured peak disk.")
    atomic(run/"RESULT.json", result)
    print(json.dumps({k: result[k] for k in ["status","modules","seconds","stdout_hex",
                                           "peak_individual_process_RSS_KiB"]}))


if __name__ == "__main__":
    main()
