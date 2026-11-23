#!/usr/bin/env python3
"""Reproduce unchanged actual C source outputs used by this mathematical track.

The executable receipt complements source-level Lean proofs; it does not replace
them. No native output is introduced as an unproved Lean premise.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--out', required=True, type=Path)
    a = p.parse_args()
    out = a.out.resolve()
    need(not out.exists(), 'Fresh experiment-owned output directory required')
    log_record = json.loads((HERE / 'C_LOG_EXECUTION.json').read_text())
    source = ROOT / log_record['source']
    need(sha(source) == log_record['source_sha256'], 'Frozen logarithm source differs')
    coeff = ROOT / 'Solutions/RHContinuation.v1/ramanujan/source_component/rh_coeff.c'
    baseline = json.loads((HERE / 'SOURCE_PROGRAM_AUDIT.json').read_text())
    need(sha(coeff) == baseline['coefficient']['source_sha256'], 'Frozen coefficient source differs')
    rows = log_record['rows']
    need(len(rows) == 4, 'Unexpected logarithm input census')
    expected_ns = [610000000000, 619000000000, 620000000000, 640000000000]
    need([r['n'] for r in rows] == expected_ns, 'Unexpected input order')
    for row in rows:
        need(all(type(row[k]) is int for k in ['n', 'output', 'two', 'k']), 'Non-integer row')
        need(2 <= row['n'] <= 2000000000000 and row['two'] == 2**row['k'] and
             row['two'] <= row['n'] < 2*row['two'], 'Outside actual proved source domain')
    out.mkdir(parents=True)
    (out / 'verified_finite_log.c').write_bytes(source.read_bytes())
    (out / 'rh_coeff.c').write_bytes(coeff.read_bytes())
    harness = '''#include <stdint.h>
#include <inttypes.h>
#include <stdio.h>
uint64_t rpc_log_upper(uint64_t);
uint64_t rh_coeff(uint64_t);
int main(void){
uint64_t ns[]={610000000000ULL,619000000000ULL,620000000000ULL,640000000000ULL};
for(unsigned i=0;i<4;i++)printf("L %"PRIu64" %"PRIu64"\\n",ns[i],rpc_log_upper(ns[i]));
for(uint64_t j=0;j<=20;j++)printf("C %"PRIu64" %"PRIu64"\\n",j,rh_coeff(j));
return 0;}
'''
    (out / 'harness.c').write_text(harness)
    command = ['cc', '-std=c11', '-O2', '-Wall', '-Wextra', '-Werror',
               '-Wno-error=empty-body', str(out / 'verified_finite_log.c'),
               str(out / 'rh_coeff.c'), str(out / 'harness.c'), '-o', str(out / 'run')]
    started = time.monotonic()
    compiled = subprocess.run(command, capture_output=True, text=True)
    (out / 'compile.stdout').write_text(compiled.stdout)
    (out / 'compile.stderr').write_text(compiled.stderr)
    need(compiled.returncode == 0, 'Actual unchanged C sources did not compile')
    executed = subprocess.run([str(out / 'run')], capture_output=True, text=True)
    (out / 'stdout').write_text(executed.stdout)
    (out / 'stderr').write_text(executed.stderr)
    need(executed.returncode == 0 and not executed.stderr, 'C execution failed')
    actual = []
    for line in executed.stdout.splitlines():
        match = re.fullmatch(r'([LC]) ([0-9]+) ([0-9]+)', line)
        need(match is not None, 'Malformed output')
        actual.append((match[1], int(match[2]), int(match[3])))
    expected = [('L', row['n'], row['output']) for row in rows]
    for j in range(21):
        lhs = sum(math.factorial(i)*math.comb(j, i) for i in range(j+1))
        rhs = sum(math.factorial(i)*math.factorial(j-i) for i in range(j+1))
        need(rhs <= lhs < 2**64, 'Coefficient outside selected mathematical domain')
        expected.append(('C', j, lhs-rhs))
    need(actual == expected, 'Execution differs from source-proved mathematical outputs')
    receipt = dict(status='PASS_ACTUAL_C_OUTPUT_ASSOCIATION', rows=len(actual),
                   seconds=time.monotonic()-started, command=command,
                   compiler_version=subprocess.check_output(['cc', '--version'], text=True).splitlines()[0],
                   compiler_binary_sha256=sha(subprocess.check_output(['which', 'cc'], text=True).strip()),
                   source_sha256=sha(source), coefficient_source_sha256=sha(coeff),
                   harness_sha256=sha(out/'harness.c'), executable_sha256=sha(out/'run'),
                   stdout_sha256=sha(out/'stdout'), script_sha256=sha(__file__),
                   logarithm_Lean='HighLogInputs.lean; generic FiniteLogUpperExecute source execution',
                   coefficient_Lean='Existing CoefficientPV.numerical/source_runs/returned_coefficient, Fin21',
                   trust='Pinned chosen C execution model and source correspondence, compiler/runtime/OS/hardware '
                         'and recorded same-source/build/run identity. Harness and Python are execution plumbing; '
                         'their checks are not the general source-first correctness proof.',
                   new_prime_count_coverage_proved=False)
    temporary = out/'RECEIPT.json.tmp'
    temporary.write_text(json.dumps(receipt, indent=2)+'\n')
    temporary.replace(out/'RECEIPT.json')
    print(json.dumps({'status': receipt['status'], 'rows': len(actual), 'seconds': receipt['seconds']}))


if __name__ == '__main__':
    main()
