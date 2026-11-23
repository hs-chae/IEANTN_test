#!/usr/bin/env python3
"""Compile one new module; caller supplies an explicit development foundation.

This is incremental development evidence. The research root separately rebuilds
the complete mathematical closure from hash-pinned source.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import resource
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
    p.add_argument('--module', required=True)
    p.add_argument('--out', required=True, type=Path)
    p.add_argument('--foundation', required=True, type=Path, action='append')
    a = p.parse_args()
    need(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', a.module), 'Bad module identifier')
    source = HERE / (a.module + '.lean')
    need(source.is_file(), 'Missing source')
    out = a.out.resolve()
    need(not out.exists(), 'Fresh output required')
    ctx = json.loads((ROOT / 'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text())
    need(sha(ctx['compiler']) == ctx['compiler_sha256'], 'Compiler identity mismatch')
    for bank in a.foundation:
        need(bank.is_dir(), 'Missing explicit foundation ' + str(bank))
    out.mkdir(parents=True)
    (out / 'objects').mkdir()
    snapshot = out / source.name
    snapshot.write_bytes(source.read_bytes())
    source_hash = sha(source)
    helper_hash = sha(__file__)
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(out / 'objects'), *map(str, a.foundation),
                                *ctx['generic_libraries']])
    command = [ctx['compiler'], '--root=' + str(out), '-j1', '-o',
               str(out / 'objects' / (a.module + '.olean')), str(snapshot)]

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (64 << 30, 64 << 30))

    started = time.monotonic()
    result = subprocess.run(['/usr/bin/time', '-v', '-o', str(out / 'resources.txt'), *command],
                            env=env, capture_output=True, text=True, preexec_fn=limits)
    (out / 'stdout').write_text(result.stdout)
    (out / 'stderr').write_text(result.stderr)
    need(sha(source) == source_hash and sha(snapshot) == source_hash, 'Source changed')
    need(sha(__file__) == helper_hash, 'Compiler wrapper changed')
    receipt = dict(status='PASS_DEV' if result.returncode == 0 else 'FAIL',
                   module=a.module, source_sha256=source_hash, helper_sha256=helper_hash,
                   compiler_sha256=ctx['compiler_sha256'], command=command,
                   LEAN_PATH=env['LEAN_PATH'], returncode=result.returncode,
                   seconds=time.monotonic() - started, per_run_limit_GiB=64,
                   development_only=True, source_first_PV_scope='See mathematical contract; '
                   'compilation alone is not program verification.')
    if result.returncode == 0:
        audits = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", result.stdout, re.S)
        need(audits, 'No theorem axiom printout')
        for name, axioms in audits:
            need(set(x.strip() for x in axioms.split(',') if x.strip()) <=
                 {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected axiom: ' + name)
        receipt['axioms'] = [dict(theorem=n, axioms=a) for n, a in audits]
        receipt['object_sha256'] = sha(out / 'objects' / (a.module + '.olean'))
    (out / 'RESULT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ['status', 'module', 'seconds', 'returncode']}))
    if result.returncode:
        print(result.stdout[-8000:])
        print(result.stderr[-3000:])
        raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
