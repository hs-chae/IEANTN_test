#!/usr/bin/env python3
"""Fresh five-source generic Gamma replay, with no application object reuse.

The actual Box first-moment consumer additionally needs the study's full source
replay; this deliberately bounded helper establishes only the five generic files.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
NAMES = ['GammaEuler', 'GammaQuadratic', 'GammaDamped', 'GammaMellin', 'GammaScaling']
EXPECTED_COMPILER = 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
EXPECTED_MATHLIB = '71a80585ee495fc24472fd0eaffc89d94e4fd8d6'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fail(message):
    raise SystemExit(message)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--context', type=Path,
                        default=REPO/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.out.exists():
        fail('Fresh owned output directory required')
    context = json.loads(args.context.read_text())
    compiler = Path(context.get('compiler', ''))
    if not compiler.is_file() or digest(compiler) != EXPECTED_COMPILER:
        fail('Pinned compiler bytes rejected')
    if context.get('pinned_mathlib_revision') != EXPECTED_MATHLIB:
        fail('Pinned Mathlib revision rejected')
    for dependency in context['generic_dependencies']:
        path = Path(dependency['path'])
        revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'],
                                           text=True).strip()
        if revision != dependency['revision']:
            fail('Generic dependency revision rejected: '+dependency['name'])
        changed = subprocess.run(['git', '-C', str(path), 'diff', '--quiet', 'HEAD', '--'],
                                 check=False)
        if changed.returncode:
            fail('Modified generic tracked source rejected: '+dependency['name'])
    libraries = [Path(x) for x in context['generic_libraries']]
    if not libraries or any(not p.is_dir() for p in libraries):
        fail('Pinned generic libraries unavailable')
    all_rows = []
    for name in ['SOURCE_FREEZE.json', 'FIRST_MOMENT_SOURCE_FREEZE.json']:
        all_rows.extend(json.loads((HERE/name).read_text())['modules'])
    selected = {row['module']: row for row in all_rows if row['module'] in NAMES}
    if set(selected) != set(NAMES):
        fail('Exact five-source frozen identity set required')
    for name in NAMES:
        path = HERE/(name+'.lean')
        if digest(path) != selected[name]['sha256']:
            fail('Source bytes rejected: '+name)
        imports = re.findall(r'^import\s+(\S+)', path.read_text(), re.M)
        if any(not (x.startswith('Mathlib.') or x in NAMES) for x in imports):
            fail('Non-generic application import rejected: '+name)
    if args.check:
        print('PASS_GENERIC_FIVE_PREFLIGHT_NO_APPLICATION_BANKS')
        return
    args.out.mkdir(parents=True, exist_ok=False)
    source = args.out/'source'
    objects = args.out/'objects'
    source.mkdir()
    objects.mkdir()
    for name in NAMES:
        shutil.copyfile(HERE/(name+'.lean'), source/(name+'.lean'))
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join(map(str, [objects, *libraries]))
    env.pop('LEAN_SRC_PATH', None)
    rows = []

    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (64 << 30, 64 << 30))
        available = sorted(os.sched_getaffinity(0))
        os.sched_setaffinity(0, available[:2])

    for name in NAMES:
        src = source/(name+'.lean')
        command = [str(compiler), '--root='+str(source), '-j2', '-o',
                   str(objects/(name+'.olean')), str(src)]
        start = time.monotonic()
        result = subprocess.run(['/usr/bin/time', '-v', *command], cwd=source,
                                env=env, capture_output=True, text=True, preexec_fn=limits)
        (args.out/(name+'.stdout')).write_text(result.stdout)
        (args.out/(name+'.stderr')).write_text(result.stderr)
        if result.returncode:
            fail('Compilation rejected: '+name)
        if digest(src) != selected[name]['sha256']:
            fail('Source changed during compilation: '+name)
        axioms = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
                            result.stdout, re.S)
        expected = {x['name'] for x in selected[name]['axioms']}
        if {x[0] for x in axioms} != expected:
            fail('Printed proof-root set rejected: '+name)
        if any(set(a.strip() for a in ax.split(',') if a.strip())-STANDARD for _, ax in axioms):
            fail('Nonstandard proof axiom rejected: '+name)
        peak = re.search(r'Maximum resident set size \(kbytes\): (\d+)', result.stderr)
        if not peak:
            fail('Peak RAM evidence missing: '+name)
        rows.append({'module': name, 'source_sha256': digest(src), 'command': command,
                     'wall_seconds': time.monotonic()-start, 'peak_RSS_KiB': int(peak.group(1)),
                     'object_sha256': digest(objects/(name+'.olean')),
                     'stdout_sha256': digest(args.out/(name+'.stdout')),
                     'stderr_sha256': digest(args.out/(name+'.stderr')),
                     'axioms': [{'name': n, 'axioms': a} for n, a in axioms]})
    receipt = {'status': 'PASS_FRESH_GENERIC_ONLY_FIVE_SOURCE_REPLAY', 'rows': rows,
               'script_sha256': digest(Path(__file__)), 'context_sha256': digest(args.context),
               'generic_libraries': list(map(str, libraries)), 'application_banks_reused': [],
               'memory_ceiling_GiB': 64, 'threads': 2, 'PV_claim': False,
               'scope': 'Five generic Gamma/scaling modules only; actual Box first moment has a separate full-source integration gate.'}
    temporary = args.out/'RECEIPT.pending.json'
    temporary.write_text(json.dumps(receipt, indent=2)+'\n')
    temporary.replace(args.out/'RECEIPT.json')
    print(receipt['status'])


if __name__ == '__main__':
    main()
