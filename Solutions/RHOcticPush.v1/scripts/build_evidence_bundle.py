#!/usr/bin/env python3
"""Archive a reviewed explicit file inventory and verify every stored byte.

This is an artifact identity check, not mathematical or program verification.
The input specification records exact source, destination, size, SHA and role.
It must be reviewed separately; no directory scan chooses publication scope.
"""
import argparse
import hashlib
import json
import re
import stat
import zipfile
from pathlib import Path, PurePosixPath


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: '+key)
        result[key] = value
    return result


def sha(data):
    return hashlib.sha256(data).hexdigest()


def relative(value):
    require(isinstance(value, str) and value != '', 'Explicit destination required')
    path = PurePosixPath(value)
    require(path.parts and not path.is_absolute() and '..' not in path.parts and
            str(path) == value and '\\' not in value, 'Canonical relative destination required')
    return value


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--spec', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    raw = args.spec.read_bytes()
    spec = json.loads(raw, object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    require(spec['status'] == 'REVIEWED_EXPLICIT_PUBLICATION_BUNDLE_INPUTS',
            'Reviewed explicit publication specification required')
    require(isinstance(spec['source_commit'], str) and
            re.fullmatch('[0-9a-f]{40}', spec['source_commit']) is not None,
            'Exact published source commit required')
    require(not args.out.exists() and args.out.parent.is_dir(), 'Use a fresh owned output directory')
    rows, seen = [], set()
    for row in spec['files']:
        dest = relative(row['destination'])
        require(dest not in seen and dest != 'BUNDLE_MANIFEST.json', 'Duplicate or reserved destination')
        seen.add(dest)
        source = Path(row['source'])
        require(source.is_absolute() and stat.S_ISREG(source.lstat().st_mode),
                'Exact regular source file required: '+str(source))
        require(isinstance(row['role'], str) and row['role'], 'Publication role required')
        data = source.read_bytes()
        require(type(row['bytes']) is int and len(data) == row['bytes'] and
                sha(data) == row['sha256'], 'Reviewed source changed: '+str(source))
        rows.append(dict(path=dest, bytes=len(data), sha256=sha(data), role=row['role']))
    manifest = dict(status='EXACT_SOURCE_EVIDENCE_BUNDLE_NOT_A_PROOF_ACCEPTANCE_RECEIPT',
                    input_spec_sha256=sha(raw), source_commit=spec['source_commit'],
                    scope=spec['scope'], files=rows)
    manifest_bytes = (json.dumps(manifest, indent=2, ensure_ascii=False)+'\n').encode()
    args.out.mkdir()
    target = args.out/'RH_LIMIT_BREAKTHROUGH_EVIDENCE.zip'
    with zipfile.ZipFile(target, 'x', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for original, row in zip(spec['files'], rows):
            data = Path(original['source']).read_bytes()
            require(len(data) == row['bytes'] and sha(data) == row['sha256'],
                    'Source changed during archival: '+row['path'])
            info = zipfile.ZipInfo(row['path'], date_time=(1980, 1, 1, 0, 0, 0))
            info.external_attr = 0o100644 << 16
            info.compress_type = zipfile.ZIP_DEFLATED
            archive.writestr(info, data)
        info = zipfile.ZipInfo('BUNDLE_MANIFEST.json', date_time=(1980, 1, 1, 0, 0, 0))
        info.external_attr = 0o100644 << 16
        info.compress_type = zipfile.ZIP_DEFLATED
        archive.writestr(info, manifest_bytes)
    with zipfile.ZipFile(target) as archive:
        require(set(archive.namelist()) == seen | {'BUNDLE_MANIFEST.json'} and
                len(archive.namelist()) == len(rows)+1, 'Archive member population changed')
        require(archive.read('BUNDLE_MANIFEST.json') == manifest_bytes, 'Archive manifest changed')
        for row in rows:
            data = archive.read(row['path'])
            require(len(data) == row['bytes'] and sha(data) == row['sha256'],
                    'Stored artifact differs: '+row['path'])
    (args.out/'BUNDLE_MANIFEST.json').write_bytes(manifest_bytes)
    result = dict(status='PASS_ALL_REVIEWED_ARCHIVE_MEMBERS_READ_BACK',
                  archive=target.name, bytes=target.stat().st_size,
                  sha256=sha(target.read_bytes()), files=len(rows),
                  uncompressed_bytes=sum(row['bytes'] for row in rows),
                  mathematical_acceptance=False)
    (args.out/'RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
