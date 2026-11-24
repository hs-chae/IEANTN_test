#!/usr/bin/env python3
"""Rehydrate disposable copied evidence and test actual archive CLIs in all modes.

Three real pack executions must reproduce the delivered archive exactly; six
negative verify cases per optimization mode must reject without a success receipt.
Only previewed disposable fixtures are deleted after the complete test succeeds.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import warnings
import zipfile


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def parse(data):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'Duplicate JSON key '+key)
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs)


def atomic(path, value):
    temp = path.with_name(path.name+'.new')
    with temp.open('x') as stream:
        json.dump(value, stream, indent=2); stream.write('\n')
        stream.flush(); os.fsync(stream.fileno())
    os.replace(temp, path)
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def run(command, out, tag):
    environment = dict(os.environ)
    environment.pop('PYTHONOPTIMIZE', None)
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    result = subprocess.run(command, capture_output=True, env=environment, timeout=120)
    (out/(tag+'.stdout')).write_bytes(result.stdout)
    (out/(tag+'.stderr')).write_bytes(result.stderr)
    return result, {'command': command, 'returncode': result.returncode,
                    'stdout_sha256': sha(result.stdout), 'stderr_sha256': sha(result.stderr)}


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--study', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args(); study = args.study.resolve(strict=True); out = args.out.resolve()
    need(not out.exists() and out.parent.is_dir(), 'Fresh disposable control output required')
    source = study/'evidence/log_archive.py'
    public_path = study/'evidence/reproduction/COPIED_FILES.json'
    archive_path = study/'evidence/reproduction/COMPILER_AUDIT_LOGS.zip'
    public_bytes, archive_bytes, source_bytes = public_path.read_bytes(), archive_path.read_bytes(), source.read_bytes()
    public = parse(public_bytes)
    need(sha(archive_bytes) == public['archive']['sha256'], 'Delivered archive identity mismatch')
    out.mkdir(); positive, negative = [], []
    with zipfile.ZipFile(archive_path) as original_archive:
        original_manifest = original_archive.read('COPIED_FILES.original.json')
        need(sha(original_manifest) == public['original_copied_manifest_sha256'], 'Original manifest identity mismatch')
        rows = parse(original_manifest)['files']
        for mode, switches in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
            fixture = out/mode/'RHOnePrimeEvolution.v1'
            (fixture/'evidence/reproduction').mkdir(parents=True)
            for row in rows:
                pure = PurePosixPath(row['path'])
                need(pure.parts[:2] == ('evidence', 'reproduction') and '..' not in pure.parts
                     and not pure.is_absolute(), 'Unsafe fixture path')
                target = fixture.joinpath(*pure.parts); target.parent.mkdir(parents=True, exist_ok=True)
                data = (original_archive.read(row['path']) if row['path'] in original_archive.namelist()
                        else (study/row['path']).read_bytes())
                need(sha(data) == row['sha256'] and len(data) == row['bytes'], 'Fixture source identity mismatch')
                target.write_bytes(data)
            manifest = fixture/'evidence/reproduction/COPIED_FILES.json'
            manifest.write_bytes(original_manifest)
            (fixture/'evidence/reproduction/RUN_SUMMARY.json').write_bytes(
                (study/'evidence/reproduction/RUN_SUMMARY.json').read_bytes())
            sentinel = out/mode/'accepted-original.log'
            sentinel.write_bytes(b'Outside copied evidence scope\n'); sentinel_hash = sha(sentinel.read_bytes())
            receipt = fixture/'evidence/PACK.json'
            command = [sys.executable, *switches, str(source), '--study', str(fixture),
                       '--mode', 'pack', '--receipt', str(receipt)]
            result, observation = run(command, out, mode+'-pack')
            need(result.returncode == 0, mode+' pack failed: '+result.stderr.decode(errors='replace'))
            pack = parse(receipt.read_text())
            need(pack['archive_sha256'] == sha(archive_bytes), 'Cross-optimization deterministic ZIP mismatch')
            need(sha(sentinel.read_bytes()) == sentinel_hash, 'Out-of-scope original evidence changed')
            (out/(mode+'-PACK.json')).write_bytes(receipt.read_bytes())
            positive.append({'mode': mode, **observation, 'archive_sha256': pack['archive_sha256'],
                             'receipt_sha256': sha(receipt.read_bytes())})
            archive = fixture/'evidence/reproduction/COMPILER_AUDIT_LOGS.zip'
            frozen_manifest, frozen_archive = manifest.read_bytes(), archive.read_bytes()
            retained = fixture/next(r['path'] for r in rows if r['path'].endswith('.lean'))
            frozen_retained = retained.read_bytes()
            for case, diagnostic in [
                ('member_count', 'Declared archive member metadata mismatch'),
                ('original_manifest_member', 'Declared archive member metadata mismatch'),
                ('storage_member', 'Wrong archive member association'),
                ('payload', 'Archive member bytes/hash mismatch'),
                ('duplicate_member', 'Wrong/duplicate/archive member order'),
                ('retained_source', 'Copied bytes changed')]:
                changed = parse(frozen_manifest)
                if case == 'member_count':
                    changed['archive']['members'] += 1
                elif case == 'original_manifest_member':
                    changed['archive']['original_manifest_member'] = 'Absent.json'
                elif case == 'storage_member':
                    next(r for r in changed['files'] if r['storage']['kind'] == 'zip-member')['storage']['member'] = 'Absent.stdout'
                elif case == 'retained_source':
                    retained.write_bytes(frozen_retained+b'\n-- negative copied evidence control\n')
                elif case == 'payload':
                    temporary = archive.with_suffix('.control.new')
                    with zipfile.ZipFile(archive) as old, zipfile.ZipFile(temporary, 'w') as new:
                        mutated = False
                        for info in old.infolist():
                            data = old.read(info.filename)
                            if not mutated and info.filename.endswith('.stdout'):
                                data += b'negative payload'; mutated = True
                            new.writestr(info, data, compresslevel=9)
                    os.replace(temporary, archive)
                elif case == 'duplicate_member':
                    with warnings.catch_warnings():
                        warnings.simplefilter('ignore', UserWarning)
                        with zipfile.ZipFile(archive, 'a') as duplicate:
                            name = duplicate.namelist()[-1]; duplicate.writestr(name, duplicate.read(name))
                if case in ('payload', 'duplicate_member'):
                    changed['archive']['sha256'] = sha(archive.read_bytes())
                    changed['archive']['bytes'] = archive.stat().st_size
                manifest.write_text(json.dumps(changed, indent=2)+'\n')
                rejected_receipt = fixture/('evidence/REJECT_'+case+'.json')
                command = [sys.executable, *switches, str(source), '--study', str(fixture),
                           '--mode', 'verify', '--receipt', str(rejected_receipt)]
                result, observation = run(command, out, mode+'-'+case)
                need(result.returncode != 0 and diagnostic in result.stderr.decode(errors='replace')
                     and not rejected_receipt.exists(), 'Negative control accepted '+mode+' '+case)
                negative.append({'mode': mode, 'case': case, 'expected_diagnostic': diagnostic, **observation})
                manifest.write_bytes(frozen_manifest); archive.write_bytes(frozen_archive)
                retained.write_bytes(frozen_retained)
            print('PASS '+mode+' actualpack +6negative controls', flush=True)
    need(public_path.read_bytes() == public_bytes and archive_path.read_bytes() == archive_bytes
         and source.read_bytes() == source_bytes, 'Original delivered evidence changed')
    need(len(positive) == 3 and len(negative) == 18, 'Incomplete actual CLI controls')
    preview = {'scope': 'Only three experiment-owned rehydrated evidence fixtures and outside-scope test sentinels',
               'targets': [str(out/mode) for mode in ['normal', 'O', 'OO']]}
    atomic(out/'CLEANUP_PREVIEW.json', preview)
    for mode in ['normal', 'O', 'OO']:
        target = out/mode
        need(target.parent == out and not target.is_symlink(), 'Invalid fixture cleanup target')
        shutil.rmtree(target)
    atomic(out/'RESULT.json', {'status': 'PASS_THREE_ACTUAL_PACK_AND18_REJECTING_VERIFY_CONTROLS_NORMAL_O_OO',
                              'scope': 'Storage controls only; not proof execution.',
                              'script_sha256': sha(Path(__file__).read_bytes()),
                              'archive_script_sha256': sha(source_bytes), 'delivered_archive_sha256': sha(archive_bytes),
                              'positive': positive, 'negative': negative,
                              'cleanup_preview_sha256': sha((out/'CLEANUP_PREVIEW.json').read_bytes()),
                              'command': [sys.executable, *sys.argv]})


if __name__ == '__main__':
    main()
