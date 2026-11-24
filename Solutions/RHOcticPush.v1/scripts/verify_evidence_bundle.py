#!/usr/bin/env python3
"""Check the downloaded/extracted bundle inventory; no proof acceptance claim."""
import argparse
import hashlib
import json
import stat
from pathlib import Path, PurePosixPath


def require(condition, message):
    if not condition:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate manifest key')
        result[key] = value
    return result


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    manifest = json.loads((root/'BUNDLE_MANIFEST.json').read_bytes(),
                          object_pairs_hook=unique,
                          parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))
    require(manifest['status'] == 'EXACT_SOURCE_EVIDENCE_BUNDLE_NOT_A_PROOF_ACCEPTANCE_RECEIPT',
            'Unexpected bundle manifest')
    expected = {'BUNDLE_MANIFEST.json'}
    for row in manifest['files']:
        name = row['path']
        path = PurePosixPath(name)
        require(path.parts and not path.is_absolute() and '..' not in path.parts and str(path) == name and
                '\\' not in name and name not in expected, 'Noncanonical or duplicate member')
        expected.add(name)
        actual = root/name
        require(stat.S_ISREG(actual.lstat().st_mode) and actual.resolve().is_relative_to(root),
                'Regular owned member required: '+name)
        data = actual.read_bytes()
        require(type(row['bytes']) is int and len(data) == row['bytes'] and
                hashlib.sha256(data).hexdigest() == row['sha256'], 'Member differs: '+name)
    actual_files = {str(path.relative_to(root)) for path in root.rglob('*') if path.is_file()}
    require(actual_files == expected, 'Extracted bundle file population differs')
    print('PASS exact downloaded bundle bytes:', len(expected)-1, 'members')
    print('Mathematical and source-program verification require the documented reproduction commands.')


if __name__ == '__main__':
    main()
