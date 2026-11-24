#!/usr/bin/env python3
"""Compile only the new canonical modules against explicitly reused proof banks.

Development check, not the final fresh transitive replay. Output paths that are
about to be compiled are unlinked from the overlay before the compiler starts.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--bank', action='append', type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise SystemExit('Fresh output directory required')
    repo = args.repository.resolve(strict=True)
    study = repo / 'Solutions/RHOnePrimeEvolution.v1'
    context = json.loads((study / 'scripts/LOCAL_CONTEXT.json').read_text())
    source, objects, logs = [args.out.resolve() / n for n in ('source', 'objects', 'logs')]
    for folder in (source, objects, logs):
        folder.mkdir(parents=True)
    for bank in args.bank:
        bank = bank.resolve(strict=True)
        for path in bank.rglob('*'):
            if path.is_file():
                target = objects / path.relative_to(bank)
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.is_symlink() or target.is_file():
                    target.unlink()
                target.symlink_to(path.resolve(strict=True))
    modules = ['IEANTN.Vocabulary.RHOnePrimeEvolution',
               'IEANTN.Nodes.CMSCosineInput.v1.Conclusions',
               'IEANTN.Nodes.PrimeGapTable.v1.Conclusions',
               'IEANTN.Nodes.RHOnePrimeEvolution.v1.Conclusions', 'OnePrimeNetwork']
    env = os.environ.copy()
    env['LEAN_PATH'] = str(objects) + ':' + context['mathlib_lean_path']
    results = []
    for module in modules:
        original = repo / (module.replace('.', '/') + '.lean') if module.startswith('IEANTN.') else study / 'OnePrimeNetwork.lean'
        frozen = source / (module.replace('.', '/') + '.lean')
        frozen.parent.mkdir(parents=True, exist_ok=True)
        frozen.write_bytes(original.read_bytes())
        obj = objects / (module.replace('.', '/') + '.olean')
        for suffix in ('.olean', '.olean.private', '.olean.server', '.ilean'):
            prior = objects / (module.replace('.', '/') + suffix)
            if prior.is_symlink() or prior.is_file():
                prior.unlink()
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = ['/usr/bin/prlimit', '--as=68719476736', '--', '/usr/bin/time', '-v',
                   context['compiler'], '--root=' + str(source), '-j2', '-o', str(obj), str(frozen)]
        start = time.monotonic()
        with (logs / (module + '.stdout')).open('wb') as out, (logs / (module + '.stderr')).open('wb') as err:
            result = subprocess.run(command, env=env, stdout=out, stderr=err)
        row = {'module': module, 'returncode': result.returncode,
               'source_sha256': hashlib.sha256(frozen.read_bytes()).hexdigest(),
               'seconds': time.monotonic() - start, 'command': command}
        results.append(row)
        print(json.dumps(row), flush=True)
        if result.returncode:
            print((logs / (module + '.stdout')).read_text()[-4000:])
            break
    okay = len(results) == len(modules) and all(r['returncode'] == 0 for r in results)
    (args.out / 'EXECUTION.json').write_text(json.dumps({
        'status': 'PASS_NEW_CANONICAL_DEV_COMPILES' if okay else 'FAILED',
        'scope': 'Development overlay of explicitly reused predecessor/new proof banks; not a clean replay or PV.',
        'banks': [str(p.resolve(strict=True)) for p in args.bank], 'results': results}, indent=2) + '\n')
    if not okay:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
