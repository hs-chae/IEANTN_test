#!/usr/bin/env python3
"""Compile the new frontier consumers against an explicitly supplied proof bank.

This incremental frontdoor reuses frozen accepted application proof objects. It is
not a claim of a fresh transitive build, official Comparator verification or PV.
The campaign's combined clean build is separate.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
MODULES = ['FiniteGapBridge', 'FiniteGapSourceConsumer', 'FiniteGapRefined',
           'HybridPrimeFrontier', 'HybridSharperPrimeFrontier', 'FiniteGapAudit', 'PopulationFrontier', 'GoldbachExtendedRange',
           'GoldbachNumericalBand', 'CanonicalFrontierTransport',
           'IEANTN.Nodes.Goldbach.v3.Conclusions', 'IEANTN.Nodes.PrimeQuantile.v4.Conclusions', 'GoldbachV3Consumer',
           'PrimeQuantileV4Consumer', 'FrontierAudit', 'CanonicalConsumerAudit']


def original_source(module):
    if module.startswith('IEANTN.'):
        return HERE.parents[2] / (module.replace('.', '/') + '.lean')
    return HERE / (module + '.lean')


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    temporary = path.with_name(path.name + '.fresh-tmp')
    with temporary.open('x') as stream:
        stream.write(json.dumps(value, indent=2, allow_nan=False)+'\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def read_context(path):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('duplicate JSON key: ' + key)
            result[key] = value
        return result

    def invalid_constant(value):
        raise ValueError('non-finite JSON constant: ' + value)

    result = json.loads(path.read_text(), object_pairs_hook=pairs,
                        parse_constant=invalid_constant)

    def finite(value):
        if isinstance(value, float) and not math.isfinite(value):
            raise ValueError('non-finite JSON number')
        if isinstance(value, dict):
            for item in value.values():
                finite(item)
        elif isinstance(value, list):
            for item in value:
                finite(item)
    finite(result)
    if not isinstance(result, dict):
        raise ValueError('compiler context must be an object')
    if not isinstance(result.get('compiler'), str) or not isinstance(result.get('compiler_sha256'), str):
        raise ValueError('compiler context string fields')
    if not isinstance(result.get('generic_libraries'), list) or not all(
            isinstance(p, str) for p in result['generic_libraries']):
        raise ValueError('generic library list must contain paths')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--context', type=Path, required=True)
    parser.add_argument('--proof-bank', type=Path, required=True)
    parser.add_argument('--extra-proof-bank', type=Path, action='append', default=[])
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--modules', nargs='+', choices=MODULES,
                        default=[m for m in MODULES if m != 'FiniteGapAudit'])
    args = parser.parse_args()
    ctx = read_context(args.context)
    if not (args.proof_bank / 'OcticOptimizedCertified.olean').is_file():
        raise ValueError('proof bank lacks frozen octic consumer')
    args.out.mkdir(parents=True, exist_ok=False)
    objects = args.out / 'objects'
    objects.mkdir()
    union = args.out / 'union'
    union.mkdir()
    sources = args.out / 'source'
    sources.mkdir()
    for module in args.modules:
        dest = sources / (module.replace('.', '/') + '.lean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(original_source(module).read_bytes())
    (args.out / 'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    (args.out / 'CONTEXT.executed.json').write_bytes(args.context.read_bytes())
    write_json(args.out / 'COMMAND.json', sys.argv)
    compiler = Path(ctx['compiler'])
    if digest(compiler) != ctx['compiler_sha256']:
        raise ValueError('compiler identity mismatch')
    env = os.environ.copy()
    # Lean chooses a top-level namespace directory, so multiple partial IEANTN
    # roots must be merged rather than merely placed next to each other.
    generic = {str(Path(p).resolve()) for p in ctx['generic_libraries']}
    providers = {}
    for bank in [*args.extra_proof_bank, args.proof_bank]:
        if str(bank.resolve()) in generic:
            continue
        for path in sorted(bank.rglob('*.olean')):
            relative = path.relative_to(bank)
            key = str(relative)
            if key in providers:
                continue
            dest = union / relative
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.symlink_to(path.resolve())
            providers[key] = {'path': str(path.resolve()), 'sha256': digest(path)}
    write_json(args.out / 'APPLICATION_OBJECT_PROVIDERS.json', providers)
    env['LEAN_PATH'] = ':'.join(map(str, [union, *ctx['generic_libraries']]))
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    rows = []
    started = time.monotonic()
    for module in args.modules:
        source = sources / (module.replace('.', '/') + '.lean')
        obj = objects / (module.replace('.', '/') + '.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = ['/usr/bin/prlimit', '--as=68719476736', '--',
                   '/usr/bin/time', '-v', str(compiler), '--root=' + str(sources),
                   '-j2', '-o', str(obj), str(source)]
        t0 = time.monotonic()
        process = subprocess.run(command, env=env, capture_output=True)
        stdout = args.out / (module + '.stdout')
        stderr = args.out / (module + '.stderr')
        stdout.write_bytes(process.stdout)
        stderr.write_bytes(process.stderr)
        row = {'module': module, 'command': command, 'seconds': time.monotonic()-t0,
               'original_source': str(original_source(module)),
               'returncode': process.returncode, 'source_sha256': digest(source),
               'stdout_sha256': digest(stdout), 'stderr_sha256': digest(stderr)}
        if obj.exists():
            row['object_sha256'] = digest(obj)
            dest = union / obj.relative_to(objects)
            dest.parent.mkdir(parents=True, exist_ok=True)
            if dest.is_symlink():
                dest.unlink()
            elif dest.exists():
                raise RuntimeError('unexpected non-symlink union object')
            dest.symlink_to(obj.resolve())
        match = re.search(rb'Maximum resident set size \(kbytes\): (\d+)', process.stderr)
        if match:
            row['peak_child_RSS_KiB'] = int(match.group(1))
        for label, key in [('User time (seconds)', 'user_seconds'),
                           ('System time (seconds)', 'system_seconds')]:
            match = re.search(re.escape(label.encode()) + rb': ([0-9.]+)', process.stderr)
            if match:
                row[key] = float(match.group(1))
        rows.append(row)
        write_json(args.out / 'PROGRESS.json', rows)
        print(module, process.returncode, f'{row["seconds"]:.2f}s', flush=True)
        if process.returncode != 0:
            raise RuntimeError('Lean compilation failed: '+module)
        if b'sorryAx' in process.stdout or b'Lean.ofReduceBool' in process.stdout:
            raise RuntimeError('unapproved axiom in printed theorem closure')
    result = {'status': 'PASS_INCREMENTAL_SOURCE_COMPILES', 'modules': rows,
              'seconds': time.monotonic()-started,
              'reproduce_sha256': digest(args.out / 'reproduce.executed.py'),
              'compiler_sha256': digest(compiler),
              'context_sha256': digest(args.context),
              'proof_bank': str(args.proof_bank.resolve()),
              'owned_disk_logical_bytes': sum(p.stat().st_size for p in args.out.rglob('*')
                                               if p.is_file() and not p.is_symlink()),
              'boundary': 'kernel-checked conditional mathematics; frozen application objects reused; not source-first PV'}
    write_json(args.out / 'RESULT.json', result)


if __name__ == '__main__':
    main()
