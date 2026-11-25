#!/usr/bin/env python3
"""Run genuine incremental Lake builds; preserve real objects/traces, never copy them."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import time

from register_lake import read_json

GIB = 2**30


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atomic_json(path, value):
    need(not path.exists(), "Fresh acceptance path required")
    temporary = path.with_suffix(path.suffix + ".pending")
    with temporary.open("x") as stream:
        json.dump(value, stream, indent=2)
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())
    os.link(temporary, path)
    temporary.unlink()


def available_ram():
    return 1024 * int(next(x.split()[1] for x in Path("/proc/meminfo").read_text().splitlines()
                           if x.startswith("MemAvailable:")))


def cgroup_path():
    row = next((line[3:] for line in Path("/proc/self/cgroup").read_text().splitlines()
                if line.startswith("0::")), None)
    need(row is not None, "Unified resource cgroup required")
    return Path("/sys/fs/cgroup") / row.lstrip("/")


def resource_state(group):
    events = dict((key, int(value)) for key, value in
                  (line.split() for line in (group / "memory.events").read_text().splitlines()))
    lean_workers = []
    for token in (group / "cgroup.procs").read_text().split():
        proc = Path("/proc") / token
        try:
            if (proc / "exe").resolve().name != "lean":
                continue
            rss = next((int(line.split()[1])*1024 for line in
                        (proc / "status").read_text().splitlines() if line.startswith("VmRSS:")), 0)
            lean_workers.append({"pid": int(token), "RSS_bytes": rss})
        except (FileNotFoundError, ProcessLookupError):
            pass
    return {"active_Lean_processes": len(lean_workers), "Lean_workers": lean_workers,
            "sampled_Lean_RSS_sum_bytes": sum(worker["RSS_bytes"] for worker in lean_workers),
            "seconds_monotonic": time.monotonic(), "MemAvailable_bytes": available_ram(),
            "cgroup_memory_current_bytes": int((group / "memory.current").read_text()),
            "cgroup_memory_peak_bytes": int((group / "memory.peak").read_text()) if (group / "memory.peak").is_file() else None,
            "cgroup_memory_events": events}


def object_inventory(directory):
    return [{"path": str(p), "sha256": sha(p), "bytes": p.stat().st_size}
            for p in sorted(directory.rglob("*.olean")) if p.is_file()]


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--run", type=Path, required=True)
    parser.add_argument("--projects", nargs="+")
    parser.add_argument("--scheduler-threads", type=int, choices=range(1, 9), default=8)
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repository = here.parents[2]
    manifest_path = here / "LAKE_PROVIDER_MANIFEST.json"
    manifest = read_json(manifest_path)
    projects = args.projects or manifest["solution_projects"]
    need(projects and len(projects) == len(set(projects)) and
         set(projects) <= set(manifest["solution_projects"]), "Unknown/duplicate project")
    need(not args.run.exists(), "Fresh run directory required")
    group = cgroup_path()
    maximum = (group / "memory.max").read_text().strip()
    need(maximum != "max" and int(maximum) <= 300 * GIB,
         "Aggregate RAM cgroup limit at most300GiB required")
    need((group / "memory.swap.max").read_text().strip() == "0", "Swap0 cgroup required")
    cpu_file = group / "cpu.max"
    cpu_quota = cpu_file.read_text().split() if cpu_file.is_file() else None
    if cpu_quota is not None:
        need(cpu_quota[0] != "max" and 0 < int(cpu_quota[0]) <= 16*int(cpu_quota[1]),
             "CPU quota at most16cores required")
    # This host does not delegate the CPU controller to user services. The
    # independently enforced process affinity still bounds all children to
    # the authorized CPU set; do not claim a nonexistent kernel CPU quota.
    affinity = sorted(os.sched_getaffinity(0))
    need(16 <= len(affinity) <= 32, "Sixteen to32 assigned CPUs required")
    need(available_ram() >= 2**40, "High-resource300GiB policy requires at least1TiB available RAM")
    need(available_ram() >= (300 + 256) * GIB, "Preserved host reserve plus run allowance unavailable")
    need(shutil.disk_usage(repository).free >= 50 * GIB, "Disk admission failed")
    guard = subprocess.run(["python3", str(here / "register_lake.py"), "--check"], capture_output=True)
    need(guard.returncode == 0, "Provider/configuration guard failed: " + guard.stderr.decode())
    context = read_json(repository / "Solutions/RHOnePrimeEvolution.v1/scripts/LOCAL_CONTEXT.json")
    pins = read_json(here.parent / "primal56_fourier/DEPENDENCY_PINS.json")
    compiler = Path(context["compiler"])
    need(sha(compiler) == pins["compiler_sha256"], "Compiler identity differs")
    need(subprocess.check_output([str(compiler), "--version"], text=True).strip() ==
         pins["compiler_version"], "Compiler version differs")
    lake = compiler.parent / "lake"
    need(lake.is_file(), "Pinned Lake missing")
    fixed_pins = {entry["name"]: entry["revision"] for entry in pins["generic_dependencies"]}
    actual_context_pins = {entry["name"]: entry["revision"] for entry in context["generic_dependency_versions"]}
    root_manifest = read_json(repository / "lake-manifest.json")
    root_pins = {entry["name"]: entry["rev"] for entry in root_manifest["packages"]}
    need(len(actual_context_pins) == len(context["generic_dependency_versions"]) and
         actual_context_pins == root_pins and all(actual_context_pins.get(name) == revision
         for name, revision in fixed_pins.items()), "Generic dependency population/pins differ")
    generic = []
    for dep in context["generic_dependency_versions"]:
        package = (repository / ".lake/packages" / dep["name"]).resolve(strict=True)
        need((package.parent / "COPY_RECEIPT.json").is_file(), "Owned private generic copy required")
        need(package != Path(dep["path"]).resolve(), "Original generic source must remain read-only")
        revision = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
        clean = subprocess.check_output(["git", "-C", str(package), "status", "--porcelain",
                                         "--untracked-files=no"], text=True)
        need(revision == dep["revision"] and not clean, "Generic pin/source changed: " + dep["name"])
        for name in projects + ["RH080Study.v1"]:
            link = repository / "Solutions" / name / ".lake/packages" / dep["name"]
            need(link.is_symlink() and link.resolve() == package,
                 "Solution generic copy association differs: " + str(link))
        generic.append({"name": dep["name"], "revision": revision, "copy": str(package)})
    args.run.mkdir(parents=True)
    files = {}
    for group_entry in manifest["groups"]:
        for entry in group_entry["modules"]:
            path = (repository / group_entry["source_root"]).joinpath(*entry["module"].split(".")).with_suffix(".lean")
            files[str(path.relative_to(repository))] = sha(path)
    # Pin all current core statements/challenges as well as every selected wrapper.
    for path in list((repository / "IEANTN").rglob("*.lean")) + [repository / "IEANTN.lean"]:
        files[str(path.relative_to(repository))] = sha(path)
    for relative in ["lakefile.toml", "lake-manifest.json", "lean-toolchain",
                     "Solutions/RHOnePrimeEvolution.v1/scripts/LOCAL_CONTEXT.json",
                     "Solutions/RH080Study.v1/primal56_fourier/DEPENDENCY_PINS.json"]:
        files[relative] = sha(repository / relative)
    for name in projects + ["RH080Study.v1"]:
        for filename in ("lakefile.toml", "lake-manifest.json", "Solution.lean", "lean-toolchain"):
            path = repository / "Solutions" / name / filename
            if path.is_file():
                files[str(path.relative_to(repository))] = sha(path)
    controller_hash = sha(Path(__file__))
    registration_hash = sha(manifest_path)
    registrar_hash = sha(here / "register_lake.py")
    initial = resource_state(group)
    lock = {"scope": "Actual ordinary Lake packaging, honestly incremental using existing genuine Lake objects/traces; no application objects copied",
            "projects": projects, "registered_project_population": manifest["solution_projects"],
            "files": files, "lake": str(lake), "lake_sha256": sha(lake),
            "compiler": str(compiler), "compiler_sha256": sha(compiler),
            "generic_dependencies": generic, "source_registration_sha256": registration_hash,
            "registrar_sha256": registrar_hash, "controller_sha256": controller_hash,
            "resource_cgroup": str(group), "cgroup_memory_max_bytes": int(maximum),
            "cgroup_swap_max_bytes": 0, "CPU_affinity": affinity, "cgroup_cpu_max": cpu_quota,
            "cpu_quota_caveat": "Not delegated when null; assigned CPU affinity is the enforced CPU bound",
            "Lake_scheduler_threads": args.scheduler_threads, "registered_compiler_threads": 2,
            "host_MemAvailable_reserve_bytes": 256 * GIB,
            "high_resource_admission_minimum_available_bytes": 2**40, "initial_resources": initial,
            "initial_existing_application_objects": {
                name: object_inventory(repository / "Solutions" / name / ".lake/build")
                for name in projects + ["RH080Study.v1"]},
            "prior_run": "lake-solutions-v1 first4 projects genuinely passed; interrupted mid-G80; partial traces preserved. New full10-project commands still run."}
    (args.run / "PLAN.json").write_text(json.dumps(lock, indent=2) + "\n")
    (args.run / "run_lake_solutions.executed.py").write_bytes(Path(__file__).read_bytes())
    env = dict(os.environ, LEAN_NUM_THREADS=str(args.scheduler_threads))
    env.pop("LEAN_PATH", None)
    rows = []
    started = time.monotonic()
    maximum_memory = initial["cgroup_memory_current_bytes"]
    minimum_available = initial["MemAvailable_bytes"]
    sample_count = 0
    maximum_lean_processes = 0
    maximum_lean_rss_sum = 0
    with (args.run / "RESOURCES.jsonl").open("x") as samples:
        for name in projects:
            need(available_ram() >= 256 * GIB, "Host reserve fell below256GiB before project")
            command = ["/usr/bin/time", "-v", "-o", str(args.run / (name + ".time")),
                       str(lake), "--no-cache", "build"]
            with (args.run / (name + ".stdout")).open("wb") as stdout, \
                 (args.run / (name + ".stderr")).open("wb") as stderr:
                before = time.monotonic()
                proc = subprocess.Popen(command, cwd=repository / "Solutions" / name,
                                        env=env, stdout=stdout, stderr=stderr, start_new_session=True)
                resource_failure = None
                abort_deadline = None
                while proc.poll() is None:
                    state = resource_state(group)
                    state.update({"project": name, "seconds": time.monotonic() - started})
                    samples.write(json.dumps(state) + "\n")
                    samples.flush()
                    sample_count += 1
                    maximum_memory = max(maximum_memory, state["cgroup_memory_current_bytes"])
                    maximum_lean_processes = max(maximum_lean_processes, state["active_Lean_processes"])
                    maximum_lean_rss_sum = max(maximum_lean_rss_sum, state["sampled_Lean_RSS_sum_bytes"])
                    minimum_available = min(minimum_available, state["MemAvailable_bytes"])
                    if state["MemAvailable_bytes"] < 256 * GIB:
                        resource_failure = "Host reserve fell below256GiB"
                        if abort_deadline is None:
                            abort_deadline = time.monotonic()+10
                        try:
                            os.killpg(proc.pid, signal.SIGKILL if time.monotonic()>abort_deadline else signal.SIGTERM)
                        except ProcessLookupError:
                            pass
                    time.sleep(0.5)
                code = proc.wait()
            metrics = args.run / (name + ".time")
            metric_text = metrics.read_text()
            rss = re.search(r"Maximum resident set size \(kbytes\): (\d+)", metric_text)
            row = {"project": name, "command": command, "returncode": code,
                   "wall_seconds": time.monotonic() - before, "resource_failure": resource_failure,
                   "GNU_maximum_resident_set_size_KiB": int(rss[1]) if rss else None,
                   "stdout_sha256": sha(args.run / (name + ".stdout")),
                   "stderr_sha256": sha(args.run / (name + ".stderr")), "time_sha256": sha(metrics)}
            rows.append(row)
            (args.run / "PROGRESS.json").write_text(json.dumps({"builds": rows, "next_project_count": len(projects)-len(rows)}, indent=2) + "\n")
            if code != 0 or resource_failure or "Exit status: 0" not in metric_text:
                atomic_json(args.run / "FAILED.json", {"status": "LAKE_BUILD_FAILED", "builds": rows})
                raise RuntimeError("Lake build failed: " + name)
            print(name + " actual Lake PASS", flush=True)
    for path, expected in files.items():
        need(sha(repository / path) == expected, "Source/configuration changed during build: " + path)
    need(sha(Path(__file__)) == controller_hash, "Controller changed during build")
    need(sha(manifest_path) == registration_hash and sha(here / "register_lake.py") == registrar_hash,
         "Registration changed during build")
    final = resource_state(group)
    need(final["cgroup_memory_events"].get("oom_kill", 0) == initial["cgroup_memory_events"].get("oom_kill", 0),
         "OOM kill occurred in packaging cgroup")
    need(len(rows) == len(projects) and all(row["returncode"] == 0 for row in rows), "Incomplete actual project execution")
    full = set(projects) == set(manifest["solution_projects"])
    result = {"status": "PASS_ACTUAL_ALL10_REGISTERED_SOLUTION_LAKE_BUILDS" if full else "PASS_ACTUAL_SELECTED_REGISTERED_SOLUTION_LAKE_BUILDS",
              "all_registered_projects_completed": full, "seconds": time.monotonic()-started,
              "projects": projects, "builds": rows, "plan_sha256": sha(args.run / "PLAN.json"),
              "controller_sha256": controller_hash, "initial_resources": initial, "final_resources": final,
              "sampled_cgroup_memory_current_max_bytes": maximum_memory,
              "kernel_cgroup_memory_peak_bytes": final["cgroup_memory_peak_bytes"],
              "exact_cgroup_peak_unavailable": final["cgroup_memory_peak_bytes"] is None,
              "sampled_active_Lean_processes_max": maximum_lean_processes,
              "sampled_Lean_RSS_sum_max_bytes": maximum_lean_rss_sum,
              "RSS_sum_caveat": "Sampled sum of worker RSS can double-count shared pages; kernel cgroup charged-memory peak is recorded separately",
              "minimum_sampled_host_MemAvailable_bytes": minimum_available,
              "resource_sample_interval_seconds": 0.5, "resource_samples": sample_count,
              "cache_provenance": "Genuine existing incremental Lake objects/traces retained; no application object copies or manufactured traces; not a cold proof replay",
              "proof_closure_audits": "Separate source-only replay receipts; ordinary packaging/core checks are not Comparator approval"}
    atomic_json(args.run / "RESULT.json", result)
    print(json.dumps({"status": result["status"], "projects": len(projects), "seconds": result["seconds"]}))


if __name__ == "__main__":
    main()
