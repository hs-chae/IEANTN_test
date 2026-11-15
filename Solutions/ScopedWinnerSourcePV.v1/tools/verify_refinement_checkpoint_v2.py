"""Verify exact published bytes and accepted component source associations.

This is a byte/receipt validator, not a Lean replay or program-PV certificate.
Original dated checkpoint validation remains available as v1.
"""
from pathlib import Path, PurePosixPath
import argparse
import json
import re
import sys
import zipfile

from verify_resumed_checkpoint_v1 import decode, digest, need


def valid_name(name):
    p = PurePosixPath(name)
    return bool(name) and not p.is_absolute() and '..' not in p.parts and '\\' not in name


def checked_files(archive, manifest):
    rows = manifest['files']
    seen = set()
    for row in rows:
        name = row['path']
        need(valid_name(name) and name not in seen, 'unique archive manifest path')
        seen.add(name)
        data = archive.read(name)
        need(len(data) == row['bytes'] and digest(data) == row['sha256'],
             'archive payload hash: '+name)
    return len(rows)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--receipt', type=Path, required=True)
    args = ap.parse_args()
    root = args.root.resolve()
    receipt = args.receipt.resolve()
    need(root.is_dir() and not receipt.exists(), 'input directory and fresh receipt')
    hashes = decode((root/'HASHES.json').read_text())['files']
    seen = set()
    for row in hashes:
        name = row['path']
        need(valid_name(name) and name not in seen, 'unique publication path')
        seen.add(name)
        path = root/name
        need(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(root),
             'owned publication file')
        data = path.read_bytes()
        need(len(data) == row['bytes'] and digest(data) == row['sha256'], 'published identity')
    directory = root/'evidence/refinement-20261115-r2'
    artifacts = decode((directory/'ARTIFACTS.json').read_text())['files']
    payload_count = 0
    for row in artifacts:
        path = root/row['path']
        need(path.is_file() and digest(path.read_bytes()) == row['sha256'] and
             path.stat().st_size == row['bytes'], 'artifact identity')
        with zipfile.ZipFile(path) as archive:
            names = archive.namelist()
            need(len(names) == len(set(names)) and all(valid_name(n) for n in names),
                 'archive unique owned paths')
            need(archive.testzip() is None, 'archive CRC')
            for manifest_name in ['MANIFEST.json', 'TEXT_SOURCE_COMPONENT_MANIFEST.json',
                                  'PUBLICATION_MANIFEST.json']:
                if manifest_name in names:
                    payload_count += checked_files(archive, decode(archive.read(manifest_name).decode()))
    with zipfile.ZipFile(root/'SCOPED_SOURCE57_ACCEPTED_WIP_CHECKPOINT_V1.zip') as archive:
        manifest = decode(archive.read('MANIFEST.json').decode())
        need(manifest['body_count'] == 57 and manifest['original_body_population'] == 68 and
             manifest['application_objects_included'] == [] and manifest['drafts_included'] == []
             and manifest['fresh57_replay'] is False and manifest['namespace_isolated'] is False,
             'exact source57 acceptance boundary')
        current = 'current/'
        index = decode(archive.read(current+
            'scoped/evaluate-source-v1/CURRENT_CONTROLS_BODY_AND_MATH_INDEX_V12.json').decode())
        need(index['aggregate_actual_whole_bodies'] == 57 and
             index['controls_actual_whole_bodies'] == 27 and
             index['numerics_actual_whole_bodies'] == 30 and
             len(index['aggregate_functions']) == len(set(index['aggregate_functions'])) == 57,
             'disjoint exact body population')
        numerical = decode(archive.read(current+index['numerics_index']['path']).decode())
        need(len(numerical['files']) == 356 and len(numerical['concrete_functions']) == 30,
             'fixed V42 source population')
        for row in numerical['files']:
            for key, pin in [('source', 'source_sha256'), ('receipt', 'receipt_sha256')]:
                name = row[key].split('/ieantn-qrh-pv-synergy-20261114/')[-1]
                need(valid_name(name) and digest(archive.read(current+name)) == row[pin],
                     'accepted numerical source/receipt association')
    status = decode((root/'STATUS.json').read_text())['refinement_current']
    need(status['original_bodies_closed'] == 57 and
         status['fresh57_replay_complete'] is False and
         status['whole_original_program_source_first_PV_complete'] is False and
         status['full_isolated_run']['acceptance'] == 'RUNNING_NOT_COMPLETE' and
         status['full_isolated_run']['new_300_extension_included'] is False and
         status['pure_kernel_comparator']['source_first_PV'] is False,
         'current explicit scope boundary')
    reports = [root/'SOURCE_REFINEMENT_PROGRESS_V7.html', directory/
               'research/analytic/SOURCE_PI_PSI300_AND_PRIME_RICH_REPORT_V2.html']
    links = 0
    for report in reports:
        html = report.read_text()
        need('<math' in html and '<script' not in html.lower(), 'offline static math')
        for href in re.findall(r'href=[\"\']([^\"\']+)', html):
            if '://' not in href and not href.startswith('#'):
                path = (report.parent/href.split('#', 1)[0]).resolve()
                need(path.is_relative_to(root) and path.is_file(), 'report link: '+href)
                links += 1
    result = dict(status='PASS_REFINEMENT_PUBLISHED_BYTES_AND_SOURCE_RECEIPT_ASSOCIATIONS',
                  qualification='NOT_A_LEAN_REPLAY_OR_WHOLE_PROGRAM_PV_ACCEPTANCE',
                  published_files=len(hashes), artifacts=len(artifacts),
                  checked_archive_payloads=payload_count, checked_local_report_links=links,
                  original_bodies=57, fixed_numerical_source_modules=356,
                  hashes_sha256=digest((root/'HASHES.json').read_bytes()),
                  validator_sha256=digest(Path(__file__).read_bytes()),
                  python_optimization=sys.flags.optimize)
    receipt.parent.mkdir(parents=True, exist_ok=True)
    pending = receipt.with_name(receipt.name+'.pending')
    need(not pending.exists(), 'fresh atomic staging receipt')
    with pending.open('x') as handle:
        handle.write(json.dumps(result, indent=2, allow_nan=False)+'\n')
    pending.replace(receipt)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
