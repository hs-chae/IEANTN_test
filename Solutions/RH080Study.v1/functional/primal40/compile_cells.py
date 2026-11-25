#!/usr/bin/env python3
"""Compile an explicit immutable subset of the generated degree80 cell proofs.

The complete study cold rebuild is separate; this controller records exactly its
selected modules and declared prerequisite object path, with no implicit fallback.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import threading
import time


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def publish(path, data):
    fd, name = tempfile.mkstemp(prefix=".cells-", suffix=".tmp", dir=path.parent)
    temp = Path(name)
    try:
        with os.fdopen(fd, "w") as stream:
            stream.write(json.dumps(data, indent=2, allow_nan=False) + "\n")
        os.link(temp, path)
    finally:
        temp.unlink()


def mem_available():
    for line in Path("/proc/meminfo").read_text().splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise ValueError("MemAvailable absent")


def tree_rss():
    # Read complete /proc PPid relations, including children launched by threads.
    children, rss = {}, {}
    for p in Path("/proc").iterdir():
        if not p.name.isdigit():
            continue
        try:
            data = dict(line.split(":", 1) for line in (p/"status").read_text().splitlines()
                        if ":" in line)
            pid, parent = int(p.name), int(data["PPid"].strip())
            children.setdefault(parent, []).append(pid)
            rss[pid] = int(data.get("VmRSS", "0 kB").split()[0])*1024
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
    pending, seen, total = [os.getpid()], set(), 0
    while pending:
        pid = pending.pop()
        if pid in seen:
            continue
        seen.add(pid)
        total += rss.get(pid, 0)
        pending.extend(children.get(pid, []))
    return total


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--compiler", type=Path, required=True)
    ap.add_argument("--lean-path", required=True)
    ap.add_argument("--run", type=Path, required=True)
    ap.add_argument("--modules", required=True, help="Comma-separated exact cell-module names")
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--per-process-gib", type=int, default=32)
    a = ap.parse_args()
    here = Path(__file__).resolve().parent
    need(not a.run.exists(), "Fresh run directory required")
    names = a.modules.split(",")
    need(1 <= a.jobs <= 8 and a.per_process_gib >= 8
         and a.jobs*a.per_process_gib <= 256, "Bounded aggregate address-space policy exceeded")
    need(len(names) == len(set(names)) and names
         and all(n.startswith("G40Cells") and n[8:].isdigit() for n in names), "Invalid module list")
    need(all((here/(n+".lean")).is_file() and not (here/(n+".lean")).is_symlink() for n in names),
         "Missing selected source")
    need(mem_available() >= 256*2**30, "Host available-RAM reserve not met")
    compiler = a.compiler.resolve(strict=True)
    version = subprocess.check_output([str(compiler), "--version"], text=True).strip()
    need("4.34.0-rc2" in version, "Wrong Lean toolchain")
    a.run.mkdir(parents=True)
    frozen, objects, logs = [a.run/x for x in ["source", "objects", "logs"]]
    for p in [frozen, objects, logs]:
        p.mkdir()
    sources = []
    for name in names:
        p = here/(name+".lean")
        q = frozen/p.name
        q.write_bytes(p.read_bytes())
        sources.append(dict(module=name, sha256=sha(q), bytes=q.stat().st_size))
    start = time.monotonic()
    stop = threading.Event()
    samples = []
    def monitor():
        while not stop.is_set():
            samples.append(dict(seconds=time.monotonic()-start, sampled_owned_tree_RSS_bytes=tree_rss(),
                                available_host_RAM_bytes=mem_available()))
            stop.wait(0.5)
    observer = threading.Thread(target=monitor, daemon=True)
    observer.start()
    environment = dict(os.environ, LEAN_PATH=str(objects.resolve())+":"+a.lean_path)
    def compile_one(row):
        name = row["module"]
        command = ["prlimit", "--as="+str(a.per_process_gib*2**30), "--",
                   "/usr/bin/time", "-v", "-o", str((logs/(name+".time")).resolve()),
                   str(compiler), "-o", str((objects/(name+".olean")).resolve()), name+".lean"]
        started = time.monotonic()
        with (logs/(name+".stdout")).open("wb") as out, (logs/(name+".stderr")).open("wb") as err:
            result = subprocess.run(command, cwd=frozen, env=environment, stdout=out, stderr=err)
        output = objects/(name+".olean")
        metrics = (logs/(name+".time")).read_text()
        peak = next((int(l.split(":", 1)[1]) for l in metrics.splitlines()
                     if "Maximum resident set size (kbytes)" in l), None)
        stdout = (logs/(name+".stdout")).read_text()
        valid = result.returncode == 0 and output.is_file() and output.stat().st_size > 0
        expected_audits = (frozen/(name+".lean")).read_text().count("#print axioms")
        audits = re.findall(r"depends on axioms: \[([^\]]*)\]", stdout)
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        valid = valid and len(audits) == expected_audits and expected_audits > 0
        valid = valid and all({v.strip() for v in audit.split(",") if v.strip()} <= allowed
                              for audit in audits)
        record = dict(module=name, command=command, returncode=result.returncode,
                      seconds=time.monotonic()-started, source_sha256=row["sha256"],
                      source_bytes=row["bytes"], peak_child_RSS_KiB=peak,
                      object_sha256=sha(output) if output.is_file() else None,
                      stdout_sha256=sha(logs/(name+".stdout")), stderr_sha256=sha(logs/(name+".stderr")),
                      metrics_sha256=sha(logs/(name+".time")), accepted=valid)
        print(json.dumps({k:record[k] for k in ["module", "returncode", "seconds", "peak_child_RSS_KiB"]}), flush=True)
        return record
    rows = []
    try:
        with ThreadPoolExecutor(max_workers=a.jobs) as pool:
            futures = [pool.submit(compile_one, row) for row in sources]
            for future in as_completed(futures):
                rows.append(future.result())
    finally:
        stop.set()
        observer.join()
    (a.run/"RSS_SAMPLES.json").write_text(json.dumps(samples, indent=2)+"\n")
    result = dict(status="PASS_EXPLICIT_SELECTED_CELL_COMPILATION" if all(r["accepted"] for r in rows)
                  and len(rows) == len(sources) else "FAILED_SELECTED_CELL_COMPILATION",
                  scope="Only the explicit cell-module subset; declared prerequisite objects are reused. This is not a full cold study replay.",
                  compiler=str(compiler), compiler_sha256=sha(compiler), compiler_version=version,
                  controller_sha256=sha(Path(__file__)), declared_LEAN_PATH=a.lean_path,
                  selected_modules=sources, jobs=a.jobs, per_process_AS_bytes=a.per_process_gib*2**30,
                  seconds=time.monotonic()-start, sampled_peak_owned_tree_RSS_bytes=max((r["sampled_owned_tree_RSS_bytes"] for r in samples), default=0),
                  observed_SIGKILL_events=sum(r["returncode"] in [-9, 137] for r in rows),
                  directory_bytes_before_final_receipt=sum(p.stat().st_size for p in a.run.rglob("*") if p.is_file()),
                  actual_runs=sorted(rows, key=lambda r:r["module"]))
    publish(a.run/"RESULT.json", result)
    need(result["status"].startswith("PASS_"), "A selected cell proof failed; inspect preserved logs")
    print(json.dumps({k:v for k,v in result.items() if k not in ["actual_runs", "selected_modules", "declared_LEAN_PATH"]}))


if __name__ == "__main__":
    main()
