#!/usr/bin/env python3
"""Reassemble downloaded parts and check their exact archive identity.

Place EVIDENCE_PARTS.json and every listed part in one directory. From there run:
  python3 reassemble_evidence.py --parts EVIDENCE_PARTS.json --out evidence.zip
Success prints PASS and the archive SHA-256. Extract the resulting ZIP afterward.
The output must be new; source parts are never changed or removed. This checks
downloaded bytes, not mathematical proofs or the authenticity of the manifest.
"""
import argparse
import hashlib
import json
import os
import re
import stat
import tempfile
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate manifest key: '+key)
        result[key] = value
    return result


def check_row(row):
    require(type(row) is dict and set(row) == {'path', 'bytes', 'sha256'},
            'Expected path, bytes and sha256')
    require(type(row['path']) is str and
            re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9._-]*', row['path']) is not None,
            'Basename-only archive and part paths required')
    require(type(row['bytes']) is int and row['bytes'] > 0, 'Positive integer byte size required')
    require(type(row['sha256']) is str and re.fullmatch(r'[0-9a-f]{64}', row['sha256']) is not None,
            'Lowercase SHA-256 required')


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    parser.add_argument('--parts', type=Path, required=True, help='Downloaded EVIDENCE_PARTS.json')
    parser.add_argument('--out', type=Path, required=True, help='Fresh output ZIP file; parent must exist')
    args = parser.parse_args()
    manifest = json.loads(args.parts.read_bytes(), object_pairs_hook=unique,
                          parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    require(type(manifest) is dict and set(manifest) == {'schema', 'archive', 'parts'} and
            manifest['schema'] == 'RH_LIMIT_BREAKTHROUGH_EVIDENCE_PARTS_V1', 'Unexpected parts manifest')
    check_row(manifest['archive'])
    parts = manifest['parts']
    require(type(parts) is list and len(parts) > 0, 'Nonempty ordered parts required')
    for row in parts:
        check_row(row)
    require(len({row['path'] for row in parts}) == len(parts) and
            manifest['archive']['path'] not in {row['path'] for row in parts}, 'Distinct part names required')
    require(sum(row['bytes'] for row in parts) == manifest['archive']['bytes'], 'Archive byte total differs')
    out = args.out.absolute()
    require(out.parent.is_dir() and not os.path.lexists(out), 'Use a fresh output ZIP in an existing directory')
    directory = args.parts.resolve().parent
    for row in parts:
        source = directory/row['path']
        require(stat.S_ISREG(source.lstat().st_mode) and source.stat().st_size == row['bytes'],
                'Regular part with exact byte size required: '+row['path'])
    fd, temporary = tempfile.mkstemp(prefix='.'+out.name+'.', suffix='.partial', dir=out.parent)
    temporary = Path(temporary)
    try:
        archive_hash = hashlib.sha256()
        archive_bytes = 0
        with os.fdopen(fd, 'wb') as target:
            for row in parts:
                part_hash = hashlib.sha256()
                part_bytes = 0
                with (directory/row['path']).open('rb') as source:
                    while block := source.read(1024*1024):
                        target.write(block)
                        part_hash.update(block)
                        archive_hash.update(block)
                        part_bytes += len(block)
                require(part_bytes == row['bytes'] and part_hash.hexdigest() == row['sha256'],
                        'Part bytes or SHA-256 differ: '+row['path'])
                archive_bytes += part_bytes
        require(archive_bytes == manifest['archive']['bytes'] and
                archive_hash.hexdigest() == manifest['archive']['sha256'], 'Complete archive SHA-256 differs')
        # A hard link publishes atomically and refuses to overwrite any existing path.
        os.link(temporary, out)
    finally:
        temporary.unlink(missing_ok=True)
    print('PASS exact archive bytes:', archive_bytes, 'SHA-256:', archive_hash.hexdigest())
    print('Created:', out)


if __name__ == '__main__':
    main()
