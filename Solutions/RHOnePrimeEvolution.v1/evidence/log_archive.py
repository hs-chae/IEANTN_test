#!/usr/bin/env python3
"""Deterministically pack and verify duplicated public reproduction logs.

Only compiler-stdout/*.stdout, compiler-stderr/*.stderr and audit-logs/*.{stdout,
stderr} from the copied evidence manifest are archived/deleted. Original accepted
run directories, JSON receipts, plans, RSS samples and source deltas are outside
the cleanup selection. This is storage verification, not new proof acceptance.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys
import zipfile
import zlib

ARCHIVE = 'evidence/reproduction/COMPILER_AUDIT_LOGS.zip'
MANIFEST = 'evidence/reproduction/COPIED_FILES.json'
ORIGINAL = 'COPIED_FILES.original.json'
STAMP = (1980, 1, 1, 0, 0, 0)
RUNS = {'unchanged244', 'historical297', 'relocated300', 'gaussian53'}


def need(value, message):
    if not value:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    return digest(path.read_bytes())


def parse(data):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'Duplicate JSON key '+key)
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=pairs)


def atomic(path, value):
    temporary = path.with_name(path.name+'.new')
    with temporary.open('x', encoding='utf-8') as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
    os.replace(temporary, path)
    directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def owned(study, relative):
    pure = PurePosixPath(relative)
    need(not pure.is_absolute() and str(pure) == relative and '..' not in pure.parts,
         'Invalid evidence path '+relative)
    need(pure.parts[:2] == ('evidence', 'reproduction'), 'Outside copied evidence '+relative)
    candidate = study.joinpath(*pure.parts)
    current = study
    for part in pure.parts:
        current = current/part
        need(not current.is_symlink(), 'Symlink evidence path '+relative)
    need(candidate.resolve().is_relative_to(study/'evidence/reproduction'), 'Escaping evidence path')
    return candidate


def rows_of(manifest):
    rows = manifest['files']; table = {}
    need(isinstance(rows, list) and len(rows) == 1833, 'Expected exact 1833-file copied population')
    for row in rows:
        path = row['path']; pure = PurePosixPath(path)
        need(path not in table and len(pure.parts) >= 4 and pure.parts[:2] == ('evidence', 'reproduction')
             and pure.parts[2] in RUNS and '..' not in pure.parts, 'Invalid/duplicate copied identity '+path)
        need(re.fullmatch('[0-9a-f]{64}', row['sha256']) is not None, 'Invalid copied hash '+path)
        need(type(row['bytes']) is int and row['bytes'] >= 0, 'Invalid copied size '+path)
        table[path] = row
    return table


def is_log(path):
    parts = PurePosixPath(path).parts
    if len(parts) != 5:
        return False
    directory, name = parts[3:]
    if directory == 'compiler-stdout':
        return name.endswith('.stdout')
    if directory == 'compiler-stderr':
        return name.endswith('.stderr')
    if directory == 'audit-logs':
        return name.endswith(('.stdout', '.stderr'))
    return False


def partition(table):
    logs = {p: r for p, r in table.items() if is_log(p)}
    retained = {p: r for p, r in table.items() if p not in logs}
    need(len(logs) == 1814 and len(retained) == 19, 'Copied log/readable partition changed')
    need(not any(PurePosixPath(p).suffix in ('.stdout', '.stderr') for p in retained),
         'Unclassified copied stdout/stderr')
    need(all(PurePosixPath(p).suffix in ('.json', '.csv', '.lean') for p in retained),
         'Unexpected retained evidence type')
    return logs, retained


def check_file(study, row):
    path = owned(study, row['path'])
    need(path.is_file() and stat.S_ISREG(path.stat().st_mode), 'Missing owned regular copied file '+row['path'])
    data = path.read_bytes()
    need(len(data) == row['bytes'] and digest(data) == row['sha256'], 'Copied bytes changed '+row['path'])
    return data


def build_zip(path, payloads):
    with path.open('xb') as stream:
        with zipfile.ZipFile(stream, 'w', compression=zipfile.ZIP_DEFLATED,
                             compresslevel=9, allowZip64=False) as archive:
            for name in sorted(payloads):
                info = zipfile.ZipInfo(name, date_time=STAMP)
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                info.compress_type = zipfile.ZIP_DEFLATED
                archive.writestr(info, payloads[name], compresslevel=9)
        stream.flush(); os.fsync(stream.fileno())


def read_zip(path, expected, original_bytes):
    """Read every member independently of the ZIP writer and check metadata/bytes."""
    with zipfile.ZipFile(path, 'r') as archive:
        members = archive.infolist(); names = [row.filename for row in members]
        need(names == sorted(expected) and len(names) == len(set(names)), 'Wrong/duplicate/archive member order')
        for member in members:
            need(member.date_time == STAMP and member.create_system == 3
                 and member.compress_type == zipfile.ZIP_DEFLATED
                 and member.external_attr >> 16 == (stat.S_IFREG | 0o644),
                 'Nondeterministic archive member metadata '+member.filename)
            data = archive.read(member.filename)
            row = expected[member.filename]
            need(len(data) == row['bytes'] and digest(data) == row['sha256'],
                 'Archive member bytes/hash mismatch '+member.filename)
        need(archive.read(ORIGINAL) == original_bytes, 'Original copied manifest not preserved byte-for-byte')
        need(archive.testzip() is None, 'Archive CRC readback failed')
    return len(members)


def verify(study):
    public = parse(owned(study, MANIFEST).read_bytes())
    need(public['status'] == 'HASHED_COPIED_EVIDENCE_WITH_ARCHIVED_DUPLICATE_LOGS_NOT_NEW_PROOF_ACCEPTANCE',
         'Unexpected archive storage manifest status')
    description = public['archive']; archive_path = owned(study, ARCHIVE)
    need(description['path'] == ARCHIVE and description['sha256'] == sha(archive_path)
         and description['bytes'] == archive_path.stat().st_size, 'Archive storage identity mismatch')
    with zipfile.ZipFile(archive_path) as archive:
        original_bytes = archive.read(ORIGINAL)
    need(digest(original_bytes) == public['original_copied_manifest_sha256'], 'Original copied manifest hash mismatch')
    original = parse(original_bytes)
    need(set(original) == {'files'}, 'Unexpected original copied manifest schema')
    old = rows_of(original); current = rows_of(public)
    need(set(old) == set(current), 'Copied population changed during archival')
    logs, retained = partition(old)
    expected = {p: {'sha256': r['sha256'], 'bytes': r['bytes']} for p, r in logs.items()}
    expected[ORIGINAL] = {'sha256': digest(original_bytes), 'bytes': len(original_bytes)}
    count = read_zip(archive_path, expected, original_bytes)
    need(description['members'] == count and description['original_manifest_member'] == ORIGINAL,
         'Declared archive member metadata mismatch')
    for name, row in current.items():
        need({key: row[key] for key in ('path', 'sha256', 'bytes')} == old[name], 'Original copied row changed '+name)
        if name in logs:
            need(row['storage'] == {'kind': 'zip-member', 'archive': ARCHIVE, 'member': name},
                 'Wrong archive member association '+name)
            need(not owned(study, name).exists(), 'Duplicated copied log remains '+name)
        else:
            need(row['storage'] == {'kind': 'file', 'path': name}, 'Wrong readable file association '+name)
            check_file(study, row)
    return {'archive_sha256': sha(archive_path), 'archive_bytes': archive_path.stat().st_size,
            'original_copied_manifest_sha256': digest(original_bytes), 'archive_members': count,
            'archived_log_files': len(logs), 'retained_readable_files': len(retained),
            'original_copied_files': len(old), 'all_members_fully_read_and_hashed': True}


def pack(study):
    manifest_path = owned(study, MANIFEST)
    original_bytes = manifest_path.read_bytes(); original = parse(original_bytes)
    need(set(original) == {'files'}, 'Packing requires unchanged original copied manifest')
    table = rows_of(original); logs, retained = partition(table)
    need(all(set(row) == {'path', 'sha256', 'bytes'} for row in table.values()),
         'Unexpected original copied row schema')
    for parent in {owned(study, name).parent for name in logs}:
        expected_children = {owned(study, name) for name in logs if owned(study, name).parent == parent}
        need(set(parent.iterdir()) == expected_children,
             'Unexpected file in copied log directory before cleanup '+str(parent))
    archive_path = owned(study, ARCHIVE)
    temporary = archive_path.with_name(archive_path.name+'.new')
    twin = archive_path.with_name(archive_path.name+'.determinism.new')
    need(not archive_path.exists(), 'Fresh log archive required')
    payloads = {name: check_file(study, row) for name, row in logs.items()}
    for row in retained.values():
        check_file(study, row)
    summary = owned(study, 'evidence/reproduction/RUN_SUMMARY.json')
    summary_hash = sha(summary)
    payloads[ORIGINAL] = original_bytes
    build_zip(temporary, payloads); build_zip(twin, payloads)
    need(sha(temporary) == sha(twin) and temporary.read_bytes() == twin.read_bytes(),
         'Two independent deterministic archive builds differ')
    expected = {name: {'bytes': len(data), 'sha256': digest(data)} for name, data in payloads.items()}
    read_zip(temporary, expected, original_bytes); read_zip(twin, expected, original_bytes)
    preview = {'status': 'VERIFIED_ARCHIVE_CLEANUP_PREVIEW_NOT_PROOF_ACCEPTANCE',
               'selection': 'Only copied compiler-stdout/*.stdout, compiler-stderr/*.stderr, audit-logs/*.{stdout,stderr} under the four named evidence/reproduction runs',
               'targets': [{'path': name, 'sha256': logs[name]['sha256'], 'bytes': logs[name]['bytes']}
                           for name in sorted(logs)],
               'original_copied_manifest_sha256': digest(original_bytes),
               'determinism_temporary_copy': {'path': str(twin.relative_to(study)), 'sha256': sha(twin)},
               'retained_readable_paths': sorted(retained),
               'outside_scope': 'Every original accepted run, proof object, mathematical source, JSON/PLAN/RSS and source-delta evidence'}
    preview_path = owned(study, 'evidence/reproduction/LOG_CLEANUP_PREVIEW.json')
    need(not preview_path.exists(), 'Fresh cleanup preview required')
    atomic(preview_path, preview)
    os.replace(temporary, archive_path)
    public = {'status': 'HASHED_COPIED_EVIDENCE_WITH_ARCHIVED_DUPLICATE_LOGS_NOT_NEW_PROOF_ACCEPTANCE',
              'original_copied_manifest_sha256': digest(original_bytes),
              'archive': {'path': ARCHIVE, 'sha256': sha(archive_path), 'bytes': archive_path.stat().st_size,
                          'members': len(payloads), 'original_manifest_member': ORIGINAL,
                          'format': 'ZIP_DEFLATED level9; lexicographic names; 1980-01-01T00:00:00; Unix regular0644'},
              'files': []}
    for row in original['files']:
        name = row['path']
        storage = ({'kind': 'zip-member', 'archive': ARCHIVE, 'member': name} if name in logs
                   else {'kind': 'file', 'path': name})
        public['files'].append({**row, 'storage': storage})
    need(manifest_path.read_bytes() == original_bytes, 'Copied manifest changed before storage update')
    atomic(manifest_path, public)
    # The verified archive now contains every byte being removed. Recheck each
    # owned duplicate against its original row immediately before unlinking it.
    for name in sorted(logs):
        check_file(study, logs[name]); owned(study, name).unlink()
    for parent in sorted({owned(study, name).parent for name in logs}, reverse=True):
        need(not any(parent.iterdir()), 'Unexpected file in copied log directory; preserve it')
        parent.rmdir()
    need(sha(twin) == public['archive']['sha256'], 'Determinism temporary archive changed')
    twin.unlink()
    need(sha(summary) == summary_hash, 'Run summary changed during log cleanup')
    result = verify(study)
    result.update({'deterministic_two_build_bytes_equal': True,
                   'cleanup_preview_sha256': sha(preview_path), 'run_summary_sha256': summary_hash})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--study', type=Path, required=True)
    parser.add_argument('--mode', choices=['pack', 'verify'], required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args(); study = args.study.resolve(strict=True)
    need(study.name == 'RHOnePrimeEvolution.v1', 'Exact owned study required')
    receipt = args.receipt.resolve()
    need(receipt.is_relative_to(study/'evidence') and receipt.parent.is_dir()
         and not receipt.exists(), 'Fresh receipt inside owned evidence directory required')
    result = pack(study) if args.mode == 'pack' else verify(study)
    result.update({'status': 'PASS_DETERMINISTIC_LOG_ARCHIVE_FULL_READBACK_AND_SCOPED_COPIED_LOG_CLEANUP',
                   'scope': 'Storage verification only, not new mathematical or source-first PV acceptance.',
                   'mode': args.mode, 'script_sha256': sha(Path(__file__).resolve()),
                   'public_manifest_sha256': sha(owned(study, MANIFEST)),
                   'command': [sys.executable, *sys.argv], 'python': sys.version,
                   'zlib_compile_version': zlib.ZLIB_VERSION, 'zlib_runtime_version': zlib.ZLIB_RUNTIME_VERSION})
    atomic(receipt, result)
    print(json.dumps(result, ensure_ascii=False))


if __name__ == '__main__':
    main()
