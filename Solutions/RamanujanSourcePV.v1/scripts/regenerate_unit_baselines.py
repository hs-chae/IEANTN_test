#!/usr/bin/env python3
"""Byte-exact regeneration before cleanup; timings are NOT matched benchmarks."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
import resource
import subprocess
import time

S = Path(__file__).resolve().parents[1]


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--study", type=Path, required=True)
    parser.add_argument("--scratch", type=Path, required=True)
    parser.add_argument("--generator", type=Path, required=True)
    parser.add_argument("--cpus", default=",".join(map(str, range(48, 64))))
    args = parser.parse_args()
    scratch = args.scratch.resolve()
    need(scratch.name == "ivy-ramanujan-source-pv-20261119" and scratch.is_dir(), "actual owned scratch root")
    output = scratch / "unit-regeneration-before-cleanup-v1"
    need(not output.exists(), "fresh regeneration directory required")
    cpus = list(map(int, args.cpus.split(",")))
    need(len(cpus) == 16 and len(set(cpus)) == 16 and set(cpus) <= os.sched_getaffinity(0), "sixteen distinct available CPUs")
    available = int(next(line.split()[1] for line in Path("/proc/meminfo").read_text().splitlines() if line.startswith("MemAvailable:"))) * 1024
    need(available > (512 + 256) * 1024**3, "host reserve plus independent native ceilings")
    output.mkdir()
    all_rows = []
    beginning = time.monotonic()
    for end in [1490000000000, 1620000000000]:
        original = args.study / "evidence" / ("finite-unit-" + str(end)) / "RUN.json"
        manifest = json.loads(original.read_text())
        need(manifest["status"] == "UNTRUSTED_NUMERICAL_GENERATION_COMPLETE" and manifest["mode"] == "unit" and manifest["end_inclusive"] == end, "exact completed original numerical baseline")
        need(manifest["chunks"] == 64 and len(manifest["records"]) == 64, "entire fixed original chunk population")
        need(manifest["source_sha256"] == sha(S / "c/generate_finite.cpp"), "unchanged actual numerical source")
        folder = output / str(end)
        folder.mkdir()

        def regenerate(row):
            index = row["chunk"]
            need(type(index) is int and 0 <= index < 64, "original integer chunk identity")
            destination = folder / (str(index) + ".bin")
            command = [str(args.generator.resolve()), str(row["begin"]), str(row["end_exclusive"]), str(destination), "unit"]

            def limits():
                resource.setrlimit(resource.RLIMIT_AS, (16 << 30, 16 << 30))
                os.sched_setaffinity(0, {cpus[index % 16]})

            started = time.monotonic()
            with (folder / (str(index) + ".stdout")).open("wb") as stdout, (folder / (str(index) + ".stderr")).open("wb") as stderr:
                result = subprocess.run(["/usr/bin/time", "-v", "-o", str(folder / (str(index) + ".rusage")), *command], stdout=stdout, stderr=stderr, preexec_fn=limits)
            need(result.returncode == 0, "regeneration failure preserved: " + str(index))
            digest = sha(destination)
            need(destination.stat().st_size == row["certificate_bytes"] and digest == row["certificate_sha256"], "byte-exact reproduction failure: " + str(index))
            return dict(end=end, chunk=index, generated_file=str(destination), command=command,
                        byte_length=destination.stat().st_size, sha256=digest, elapsed_seconds=time.monotonic() - started,
                        original_manifest=str(original), original_manifest_sha256=sha(original),
                        original_generated_file=str(scratch / ("finite-unit-" + str(end)) / (str(index) + ".bin")))

        need(sorted(row["chunk"] for row in manifest["records"]) == list(range(64)), "every original chunk exactly once")
        with ThreadPoolExecutor(max_workers=16) as pool:
            rows = list(pool.map(regenerate, manifest["records"]))
        all_rows.extend(rows)
        print(json.dumps({"end": end, "byte_identical_chunks": len(rows)}), flush=True)
    receipt = dict(status="PASS_BOTH_FULL_UNIT_BASELINES_BYTE_EXACT_REGENERATION", rows=all_rows,
                   source_sha256=sha(S / "c/generate_finite.cpp"), generator_sha256=sha(args.generator),
                   script_sha256=sha(__file__), elapsed_seconds=time.monotonic() - beginning, cpus=cpus,
                   performance_comparison=False, deletion_performed=False,
                   mathematical_verification_claim="ordinary deterministic data regeneration; not source-first PV")
    temporary = output / "RESULT.json.tmp"
    temporary.write_text(json.dumps(receipt, indent=2) + "\n")
    temporary.replace(output / "RESULT.json")
    print(json.dumps({"status": receipt["status"], "result": str(output / "RESULT.json")}))


if __name__ == "__main__":
    main()
