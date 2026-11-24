#!/usr/bin/env python3
"""Fresh scoped Lean compilation; local context reuse is explicit, not clean replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--objects', type=Path, action='append', default=[])
    args = parser.parse_args()
    context = json.loads(Path(__file__).with_name('LOCAL_CONTEXT.json').read_text())
    if args.output.exists():
        raise SystemExit('Output directory must be fresh')
    source = args.source.resolve(strict=True)
    output = args.output.resolve()
    output.mkdir(parents=True)
    frozen = output / source.name
    frozen.write_bytes(source.read_bytes())
    obj = output / (source.stem + '.olean')
    command = ['/usr/bin/prlimit', '--as=68719476736', '--',
               '/usr/bin/time', '-v', context['compiler'], '-j2',
               '--root=' + str(output), '-o', str(obj), str(frozen)]
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(p.resolve(strict=True)) for p in args.objects] +
                               [context['accepted_octic_union'], context['mathlib_lean_path']])
    start = time.monotonic()
    with (output / 'stdout').open('wb') as out, (output / 'stderr').open('wb') as err:
        result = subprocess.run(command, env=env, stdout=out, stderr=err)
    receipt = {'status': 'COMPILED' if result.returncode == 0 else 'FAILED',
               'returncode': result.returncode, 'command': command,
               'source_sha256': digest(frozen), 'source': str(source),
               'executed_source': str(frozen),
               'compiler_sha256': digest(Path(context['compiler'])),
               'seconds': time.monotonic() - start,
               'environment': {'LEAN_PATH': env['LEAN_PATH']},
               'stdout_sha256': digest(output / 'stdout'),
               'stderr_sha256': digest(output / 'stderr'),
               'object_sha256': digest(obj) if obj.exists() else None,
               'trust': 'Scoped fresh compilation using pinned predecessor objects; not a clean transitive rebuild or source-first PV.'}
    (output / 'EXECUTION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ('status', 'returncode', 'seconds')}))
    if result.returncode:
        print((output / 'stdout').read_text()[-6000:])
        raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
