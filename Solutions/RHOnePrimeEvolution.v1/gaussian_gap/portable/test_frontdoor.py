#!/usr/bin/env python3
"""Exercise the actual portable check-only CLI, including Python -O and -OO.

These controls test source/dependency guards. They do not execute Lean proofs.
Each case uses a disposable byte-copy of the supplied frozen packet; originals
are rehashed before a fresh atomic success receipt can be published.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strict_json(text):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, 'Duplicate JSON key '+key)
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs)


def atomic(path, value):
    temporary = path.with_name(path.name+'.new')
    with temporary.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def inventory(packet):
    return {str(path.relative_to(packet)): sha(path)
            for path in sorted(packet.rglob('*'))
            if path.is_file() and '__pycache__' not in path.parts}


def mutate(packet, name, manifest):
    """Change only an owned fixture and return extra CLI arguments."""
    row = manifest['modules'][0]
    source = packet/row['path']
    if name == 'missing_source':
        source.unlink()
    elif name == 'modified_source':
        source.write_bytes(source.read_bytes()+b'\n-- negative source control\n')
    elif name == 'duplicate_identity':
        manifest['modules'].append(dict(row))
    elif name == 'wrong_import_association':
        row['imports'] = ['Init']
    elif name == 'missing_provider':
        providers = {dep for item in manifest['modules'] for dep in item['imports']}
        provider = next(item for item in manifest['modules']
                        if item['module'] in providers and item['module'] not in manifest['roots'])
        manifest['modules'].remove(provider)
        replacement=packet/'source/RemovedProviderReplacement.lean'
        replacement.write_text('def removedProviderReplacement : Nat := 0\n')
        manifest['modules'].append({'module':'RemovedProviderReplacement',
            'path':'source/RemovedProviderReplacement.lean','sha256':sha(replacement),'imports':[]})
    elif name == 'invalid_source_path':
        row['path'] = '../escape.lean'
    elif name == 'invalid_module_identity':
        row['module'] = '../escape'
    elif name == 'incomplete_count':
        manifest['module_count'] -= 1
    elif name == 'below_minimum_count':
        manifest['module_count'] = 52
        manifest['modules'].pop()
    elif name == 'missing_root_provider':
        manifest['roots'].append('AbsentApplicationProvider')
    elif name == 'application_cycle':
        source.write_bytes(('import '+row['module']+'\n').encode()+source.read_bytes())
        row['sha256'] = sha(source)
        row['imports'].insert(0, row['module'])
    elif name == 'unreachable_source':
        orphan = packet/'source/UnreachableFrontdoorControl.lean'
        orphan.write_text('def unreachableFrontdoorControl : Nat := 0\n')
        manifest['modules'].append({'module': 'UnreachableFrontdoorControl',
                                   'path': 'source/UnreachableFrontdoorControl.lean',
                                   'sha256': sha(orphan), 'imports': []})
        manifest['module_count'] += 1
    elif name == 'symlink_source':
        backing = packet/'symlink-target.lean'
        source.rename(backing)
        source.symlink_to(backing)
    elif name == 'source_ledger_mutation':
        target=packet/'SOURCE_LEDGER.html'
        target.write_bytes(target.read_bytes()+b'\n<!-- changed source provenance -->\n')
    elif name in ('controller_mutation', 'audit_runner_mutation'):
        target = packet/('rebuild_closure.py' if name == 'controller_mutation' else 'verify_fresh.py')
        target.write_bytes(target.read_bytes()+b'\n# negative controller identity control\n')
    elif name == 'duplicate_json_key':
        raw = (packet/'SOURCE_MANIFEST.json').read_text()
        (packet/'SOURCE_MANIFEST.json').write_text('{"module_count":53,'+raw.lstrip()[1:])
        return []
    elif name in ('valid', 'bad_jobs_zero', 'bad_jobs_high', 'bad_jobs_negative',
                  'bad_jobs_type', 'abbreviated_flag', 'missing_generic_package',
                  'duplicate_generic_package', 'invalid_generic_path', 'wrong_compiler'):
        return []
    else:
        raise ValueError('Unknown control '+name)
    (packet/'SOURCE_MANIFEST.json').write_text(json.dumps(manifest, indent=2)+'\n')
    return []


CASES = [
    ('valid', None),
    ('missing_source', 'Expected owned regular source'),
    ('modified_source', 'Source hash mismatch'),
    ('duplicate_identity', 'Duplicate module identity'),
    ('wrong_import_association', 'Import association mismatch'),
    ('missing_provider', 'Missing application import'),
    ('invalid_source_path', 'Invalid source path'),
    ('invalid_module_identity', 'Invalid module identity'),
    ('incomplete_count', 'Incomplete selected application manifest'),
    ('below_minimum_count', 'Incomplete selected application manifest'),
    ('missing_root_provider', 'Missing application import'),
    ('application_cycle', 'Application import cycle'),
    ('unreachable_source', 'Unreachable or omitted application source'),
    ('symlink_source', 'Expected owned regular source'),
    ('controller_mutation', 'Controller identity mismatch rebuild_closure.py'),
    ('audit_runner_mutation', 'Controller identity mismatch verify_fresh.py'),
    ('source_ledger_mutation', 'Controller identity mismatch SOURCE_LEDGER.html'),
    ('duplicate_json_key', 'Duplicate JSON key module_count'),
    ('bad_jobs_zero', 'Worker count must be1..4'),
    ('bad_jobs_high', 'Worker count must be1..4'),
    ('bad_jobs_negative', 'Worker count must be1..4'),
    ('bad_jobs_type', 'invalid int value'),
    ('abbreviated_flag', 'unrecognized arguments: --check-on'),
    ('missing_generic_package', 'Incomplete generic dependency set'),
    ('duplicate_generic_package', 'Duplicate generic package'),
    ('invalid_generic_path', 'Generic library path must end'),
    ('wrong_compiler', 'Pinned Lean4.34.0-rc2 required'),
]


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--compiler', type=Path, required=True)
    parser.add_argument('--generic-lean-path', required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    packet, out = args.packet.resolve(strict=True), args.out.resolve()
    require(not out.exists() and out.parent.is_dir(), 'Fresh owned output directory required')
    manifest = strict_json((packet/'SOURCE_MANIFEST.json').read_text())
    require(manifest['module_count'] == 53 and len(manifest['modules']) == 53,
            'This campaign requires the frozen 53-module packet')
    before = inventory(packet)
    require('reproduce.py' in before, 'Actual CLI frontdoor required')
    out.mkdir()
    work = out/'disposable-fixtures'
    work.mkdir()
    cases, failures = [], []
    child_environment = dict(os.environ)
    child_environment.pop('PYTHONOPTIMIZE', None)
    child_environment['PYTHONDONTWRITEBYTECODE'] = '1'
    for mode, switches in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        for name, diagnostic in CASES:
            tag = mode+'-'+name
            fixture = work/tag
            shutil.copytree(packet, fixture, ignore=shutil.ignore_patterns('__pycache__'))
            # The real packet is read-only; make only its disposable copy mutable.
            for copied in fixture.rglob('*'):
                copied.chmod(copied.stat().st_mode | 0o200)
            local_manifest = strict_json((fixture/'SOURCE_MANIFEST.json').read_text())
            mutate(fixture, name, local_manifest)
            libraries = args.generic_lean_path
            compiler = args.compiler.resolve(strict=True)
            extra = []
            if name.startswith('bad_jobs_'):
                extra = ['--jobs', {'bad_jobs_zero': '0', 'bad_jobs_high': '5',
                                   'bad_jobs_negative': '-1', 'bad_jobs_type': 'two'}[name]]
            elif name == 'abbreviated_flag':
                extra = ['--check-on']
            elif name == 'missing_generic_package':
                libraries = ':'.join(libraries.split(':')[1:])
            elif name == 'duplicate_generic_package':
                libraries += ':'+libraries.split(':')[0]
            elif name == 'invalid_generic_path':
                libraries = str(fixture)
            elif name == 'wrong_compiler':
                compiler = fixture/'wrong-lean'
                compiler.write_text('#!/bin/sh\nprintf "Lean (version 0.0.0)\\n"\n')
                compiler.chmod(0o700)
            command = [sys.executable, *switches, str(fixture/'reproduce.py'),
                       '--compiler', str(compiler), '--generic-lean-path', libraries,
                       '--check-only', *extra]
            start = time.monotonic()
            run = subprocess.run(command, capture_output=True, timeout=120, env=child_environment)
            (out/(tag+'.stdout')).write_bytes(run.stdout)
            (out/(tag+'.stderr')).write_bytes(run.stderr)
            stdout, stderr = run.stdout.decode('utf-8', errors='replace'), run.stderr.decode('utf-8', errors='replace')
            okay = run.returncode == 0 if diagnostic is None else run.returncode != 0 and diagnostic in stderr
            if diagnostic is None and okay:
                result = strict_json(stdout)
                okay = (result['status'] == 'PASS_SOURCE_AND_GENERIC_IDENTITIES_ONLY_NOT_PROOF_EXECUTION'
                        and result['modules'] == 53
                        and result['manifest_sha256'] == before['SOURCE_MANIFEST.json']
                        and result['compiler_sha256'] == sha(compiler))
            acceptance_paths = [p for p in fixture.rglob('RESULT.json')]
            okay = okay and not acceptance_paths
            after = inventory(fixture)
            changes = {path: {'original_sha256': before.get(path), 'fixture_sha256': after.get(path)}
                       for path in sorted(set(before) | set(after)) if before.get(path) != after.get(path)}
            case = {'mode': mode, 'case': name, 'passed': okay, 'command': command,
                    'returncode': run.returncode, 'expected_diagnostic': diagnostic,
                    'seconds': time.monotonic()-start,
                    'fixture_inputs': {str(p.relative_to(fixture)): sha(p) for p in
                                       [fixture/'reproduce.py', fixture/'SOURCE_MANIFEST.json',
                                        fixture/'rebuild_closure.py', fixture/'verify_fresh.py']},
                    'stdout_sha256': sha(out/(tag+'.stdout')),
                    'stderr_sha256': sha(out/(tag+'.stderr')),
                    'exact_fixture_changes': changes,
                    'fixture_symlinks': {str(p.relative_to(fixture)): str(p.readlink())
                                         for p in fixture.rglob('*') if p.is_symlink()},
                    'unexpected_acceptance_paths': [str(p.relative_to(fixture)) for p in acceptance_paths]}
            atomic(out/(tag+'.json'), case)
            cases.append(case)
            if not okay:
                failures.append(tag)
                print('FAIL '+tag+': '+stderr[:500], flush=True)
            else:
                print('PASS '+tag, flush=True)
    require(inventory(packet) == before, 'Original packet changed during controls')
    atomic(out/'OBSERVATIONS.json', {'cases': cases, 'failures': failures})
    require(not failures, 'Rejected frontdoor control cases: '+', '.join(failures))
    cleanup = {'scope': 'Only regenerable experiment-owned byte-copies of the frozen packet',
               'root': str(work), 'targets': [str(p.relative_to(work)) for p in sorted(work.iterdir())],
               'files': sum(1 for p in work.rglob('*') if p.is_file()),
               'bytes': sum(p.stat().st_size for p in work.rglob('*') if p.is_file()),
               'original_packet_unchanged': True}
    atomic(out/'CLEANUP_PREVIEW.json', cleanup)
    require(work.parent == out and work.name == 'disposable-fixtures' and not work.is_symlink(),
            'Cleanup target escaped owned output')
    shutil.rmtree(work)
    require(not work.exists(), 'Disposable fixture cleanup incomplete')
    atomic(out/'CLEANUP_RESULT.json', {'status': 'PASS_REMOVED_ONLY_PREVIEWED_REGENERABLE_FIXTURES',
                                     'preview_sha256': sha(out/'CLEANUP_PREVIEW.json')})
    receipt = {'status': 'PASS_ACTUAL_CHECK_ONLY_CLI_GUARDS_NORMAL_O_OO_NOT_PROOF_EXECUTION',
               'scope': 'Source/dependency/CLI negative controls; full 53-module proof replay is separate.',
               'case_count': len(cases), 'cases_per_mode': len(CASES), 'failures': [],
               'harness_sha256': sha(Path(__file__).resolve()), 'python': sys.version,
               'invocation': [sys.executable, *sys.argv], 'packet': str(packet),
               'original_packet_hashes': before,
               'observations_sha256': sha(out/'OBSERVATIONS.json'),
               'cleanup_sha256': sha(out/'CLEANUP_RESULT.json')}
    atomic(out/'RESULT.json', receipt)
    print(receipt['status']+' '+str(len(cases)))


if __name__ == '__main__':
    main()
