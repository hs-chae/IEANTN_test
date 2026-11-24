#!/usr/bin/env python3
"""Build and execute the actual fixed-input driver, without claiming PV.

The source binding and static-initialization proofs are separate artifacts.
A successful native execution is not a proof of the count or of its agreement
with the formal execution model. This receipt preserves the actual output word
for the pending complete source-first refinement.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import sys
import time

S = Path(__file__).resolve().parent
COUNTER_SHA = '85326ecb93d86c693d980352ebde59a350eef89b4f367c88b65fa88f58d991dd'
DRIVER_SHA = '011738a2ee9879f25d3b24bf7b134ba20825105872a3e3d26d1a082db72140f7'


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--cc', default='cc')
    parser.add_argument('--cpu', type=int, default=8)
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists(), 'fresh owned execution directory required')
    need(args.cpu in os.sched_getaffinity(0), 'selected CPU unavailable')
    counter = S / 'c' / 'verified_quotient_count.c'
    driver = S / 'c' / 'verified_quotient_driver_high.c'
    need(sha(counter) == COUNTER_SHA, 'counter source changed')
    need(sha(driver) == DRIVER_SHA, 'driver source changed')
    found = shutil.which(args.cc)
    need(found is not None, 'C compiler unavailable')
    compiler = Path(found).resolve()
    out.mkdir(parents=True)
    sources = out / 'source'
    sources.mkdir()
    shutil.copy2(counter, sources / counter.name)
    shutil.copy2(driver, sources / driver.name)
    version = subprocess.check_output([str(compiler), '--version'], text=True)
    (out / 'compiler-version').write_text(version)
    executable = out / 'driver-high'
    compile_command = [str(compiler), '-std=c11', '-O2', '-Wall',
                       str(sources / counter.name), str(sources / driver.name),
                       '-o', str(executable)]
    start = time.monotonic()
    with (out / 'compile-stdout').open('wb') as stdout, (out / 'compile-stderr').open('wb') as stderr:
        build = subprocess.run(compile_command, stdout=stdout, stderr=stderr, check=False)
    need(build.returncode == 0, 'C compilation failed; outputs preserved')
    compile_seconds = time.monotonic() - start
    command = ['/usr/bin/time', '-v', '-o', str(out / 'rusage'),
               '/usr/bin/prlimit', '--as=' + str(64 << 30), '--',
               '/usr/bin/taskset', '-c', str(args.cpu), str(executable)]
    start = time.monotonic()
    with (out / 'stdout.bin').open('wb') as stdout, (out / 'stderr').open('wb') as stderr:
        run = subprocess.run(command, stdout=stdout, stderr=stderr, check=False, timeout=600)
    seconds = time.monotonic() - start
    output = (out / 'stdout.bin').read_bytes()
    receipt = {
        'status': 'NATIVE_DRIVER_EXECUTED_NOT_YET_ACCEPTED',
        'source_first_PV_complete': False, 'numerical_output_is_a_proved_count': False,
        'fixed_source_input': 1490000000000,
        'source_model_proof_status': 'separate Lean obligations; count certificate still running',
        'counter_sha256': COUNTER_SHA, 'driver_sha256': DRIVER_SHA,
        'compiler': str(compiler), 'compiler_sha256': sha(compiler),
        'compiler_version_sha256': sha(out / 'compiler-version'),
        'compile_command': compile_command, 'compile_seconds': compile_seconds,
        'compile_exit_code': build.returncode, 'executable_sha256': sha(executable),
        'execution_command': command, 'execution_exit_code': run.returncode,
        'execution_seconds': seconds, 'output_bytes': len(output),
        'output_sha256': sha(out / 'stdout.bin'), 'stderr_sha256': sha(out / 'stderr'),
        'rusage_sha256': sha(out / 'rusage'), 'architecture': platform.machine(),
        'word_byte_order': sys.byteorder,
        'input': 1490000000000, 'capacity_each': 1500000,
        'array_storage_bytes_total': 2 * 1500000 * 8,
        'remaining_trust_and_obligations': [
            'actual new driver main source/model successful-run proof',
            'source-linked numerical execution/output proof',
            'independent frontend interpretation remains an explicit contract',
            'generic C compiler/runtime/OS/stdio/ABI and hardware contracts',
        ],
    }
    (out / 'RUN.json').write_text(json.dumps(receipt, indent=2) + '\n')
    need(run.returncode == 0, 'driver returned failure; attempt preserved')
    need(len(output) == 8, 'driver did not emit exactly one uint64 word')
    need(sha(counter) == COUNTER_SHA and sha(driver) == DRIVER_SHA, 'source changed during execution')
    receipt.update({'status': 'ORDINARY_NATIVE_DRIVER_EXECUTION_NOT_YET_SOURCE_FIRST_PV',
                    'emitted_word': int.from_bytes(output, byteorder=sys.byteorder, signed=False)})
    temporary = out / 'RESULT.json.tmp'
    temporary.write_text(json.dumps(receipt, indent=2) + '\n')
    temporary.replace(out / 'RESULT.json')
    print(json.dumps({'status': receipt['status'], 'emitted_word': receipt['emitted_word'],
                      'seconds': seconds, 'out': str(out)}))


if __name__ == '__main__':
    main()
