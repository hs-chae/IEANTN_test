#!/usr/bin/env python3
"""Regenerate deterministic octic proposals/proof text in owned scratch.

mpmath is an untrusted proposer. Byte identity with the frozen mathematical
sources is checked here; the full clean Lean pipeline supplies proof acceptance.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
import mpmath

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
ENDPOINT = REPO/'Solutions/RHOcticPush.v1/moments/endpoint'
GENERATORS = ['generate_endpoints.py', 'generate_logs.py', 'generate_cells.py',
              'generate_blocks.py', 'generate_assembly.py']
PROPOSALS = ['ENDPOINT_PROPOSALS.json', 'LOG_PROPOSALS.json', 'CELL_PROPOSALS.json']


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists() and not out.is_relative_to(REPO), 'fresh separate regeneration output')
    need(mpmath.__version__ == '1.3.0', 'pinned untrusted proposer mpmath1.3.0')
    controller_sha256 = sha(__file__)
    freeze = json.loads((ENDPOINT/'SOURCE_ROOTS.json').read_text())
    modules = freeze['modules']
    need(len(modules) == 128 and len({row['module'] for row in modules}) == 128,
         'all128 frozen mathematical identities')
    out.mkdir(parents=True)
    generated, logs = out/'generated', out/'logs'
    generated.mkdir()
    logs.mkdir()
    rows = []
    for row in modules:
        source = REPO/row['source']
        need(source.parent == ENDPOINT and sha(source) == row['sha256'],
             'frozen endpoint source identity')
        shutil.copy2(source, generated/source.name)
    for name in GENERATORS+PROPOSALS:
        shutil.copy2(ENDPOINT/name, generated/name)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    started = time.monotonic()

    def invoke(script, mode, check):
        label = str(len(rows))+'-'+script.removesuffix('.py')+'-'+('check' if check else 'write')
        command = ['/usr/bin/prlimit', '--as='+str(64 << 30), '--', '/usr/bin/time', '-v',
                   sys.executable, '-B', *mode, str(generated/script), *(['--check'] if check else [])]
        begin = time.monotonic()
        process = subprocess.run(command, env=env, cwd=generated, capture_output=True, text=True)
        stdout, stderr = logs/(label+'.stdout'), logs/(label+'.stderr')
        stdout.write_text(process.stdout)
        stderr.write_text(process.stderr)
        match = re.search(r'Maximum resident set size \(kbytes\): (\d+)', process.stderr)
        need(process.returncode == 0 and match is not None,
             'actual deterministic generator failed:'+label)
        rows.append({'script': script, 'mode': mode, 'check': check, 'command': command,
            'returncode': process.returncode, 'seconds': time.monotonic()-begin,
            'peak_child_RSS_KiB': int(match[1]),
            'stdout': str(stdout.relative_to(out)), 'stderr': str(stderr.relative_to(out)),
            'stdout_sha256': sha(stdout), 'stderr_sha256': sha(stderr)})
        (out/'PROGRESS.json').write_text(json.dumps({'completed_actual_commands': len(rows)}, indent=2)+'\n')

    for name in GENERATORS:
        invoke(name, [], False)
    for mode in [[], ['-O'], ['-OO']]:
        for name in GENERATORS:
            invoke(name, mode, True)
    actual = []
    for row in modules:
        target = generated/Path(row['source']).name
        need(sha(target) == row['sha256'] == sha(REPO/row['source']),
             'regenerated mathematical source differs:'+row['module'])
        actual.append({'module': row['module'], 'original': row['source'],
                       'generated': str(target.relative_to(out)), 'sha256': sha(target)})
    for name in PROPOSALS:
        need(sha(generated/name) == sha(ENDPOINT/name), 'regenerated numerical proposal differs:'+name)
    need(sha(__file__) == controller_sha256, 'controller source unchanged during regeneration')
    need(len(rows) == 20, 'all five writes and fifteen three-mode checks')
    receipt = {'status': 'PASS_DETERMINISTIC_REGENERATION_ALL128_MATH_SOURCES_AND_PROPOSALS',
        'controller_sha256': controller_sha256, 'source_freeze_sha256': sha(ENDPOINT/'SOURCE_ROOTS.json'),
        'parameters': {'mpmath_version': mpmath.__version__, 'decimal_digits': 100,
            'random_seed': None, 'endpoints': 7301, 'cells': 7300, 'blocks': 115,
            'grid': '0..10step.01;10..100step.05;100..1000step.2',
            'endpoint_log_scale': 10**8, 'cell_scale': 10**12},
        'actual_commands': rows, 'exact_mathematical_source_hashes': actual,
        'seconds': time.monotonic()-started,
        'peak_individual_child_RSS_KiB': max(row['peak_child_RSS_KiB'] for row in rows),
        'owned_regular_bytes_before_result': sum(p.stat().st_size for p in out.rglob('*')
            if p.is_file() and not p.is_symlink()),
        'numerical_proof_acceptance': 'Separate complete source-only Lean kernel pipeline required',
        'source_first_PV_claim': False}
    pending = out/'RESULT.pending.json'
    pending.write_text(json.dumps(receipt, indent=2, allow_nan=False)+'\n')
    os.replace(pending, out/'RESULT.json')
    print(receipt['status'], flush=True)


if __name__ == '__main__':
    main()
