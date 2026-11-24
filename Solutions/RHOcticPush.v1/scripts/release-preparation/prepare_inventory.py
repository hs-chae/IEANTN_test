#!/usr/bin/env python3
"""Prepare, but never self-approve, an exact final bundle inventory.

Publication lists are explicit reviewed manifests, in chronological order. A
later list may replace the same publication path; every replacement is exposed
in COLLISIONS.json. Immutable analytic/finite packet files cannot be replaced.
No filesystem traversal selects publication files. No proof objects are added.
"""
import argparse
import re
from pathlib import Path
from common import checked, identity, need, read, relative, save, sha

ANALYTIC_OUTER = ['SOURCE_PACKET.json', 'SOURCE_IDENTITIES_739.json',
    'READ_DEPENDENCIES_739.json', 'RUNTIME_COMPATIBILITY.json',
    'ORIGINAL_SOURCE_PACKET739_V3.json']
PREFIX = 'Solutions/RHOcticPush.v1/'
ANALYTIC_SHA = '9d61faaa0ef609e128711a4866529cbf37bbbc77bd08d4830d31af263a347882'
FINITE_SHA = 'ac1a4a073efed04f86053dd54d1cf6bc36b8c0d125548c1c4ced8e15bae291ae'
FORBIDDEN = {'.git', '.lake', '__pycache__', 'private', 'memory', 'human_input'}


def public_path(value):
    value = relative(value)
    path = Path(value)
    need(not set(path.parts) & FORBIDDEN and path.suffix not in
        {'.olean', '.ilean', '.o', '.a', '.so', '.pyc'},
        'object/cache/private path excluded: '+value)
    return value


def rows(path):
    obj = read(path)
    if type(obj) is list:
        return obj
    need(type(obj) is dict, 'explicit manifest object/list required')
    candidates = [obj[key] for key in ['rows', 'files'] if type(obj.get(key)) is list]
    need(len(candidates) == 1, 'one explicit row list required: '+str(path))
    return candidates[0]


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    parser.add_argument('--publication', type=Path, required=True)
    parser.add_argument('--publication-list', action='append', type=Path, required=True)
    parser.add_argument('--analytic', type=Path, required=True)
    parser.add_argument('--finite', type=Path, required=True)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--reports-list', type=Path)
    parser.add_argument('--extras-list', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    need(re.fullmatch('[0-9a-f]{40}', args.source_commit), 'exact source commit argument required')
    need(not args.out.exists() and args.out.parent.is_dir(), 'fresh preparation output directory')
    selected, provenance, collisions = {}, [], []
    for manifest in args.publication_list:
        provenance.append(dict(kind='publication', path=str(manifest.resolve()), **identity(manifest)))
        local_seen = set()
        for row in rows(manifest):
            path = public_path(row['path'])
            need(path not in local_seen, 'duplicate manifest publication path: '+path)
            local_seen.add(path)
            need(type(row['bytes']) is int and row['bytes'] >= 0 and
                 type(row['sha256']) is str and re.fullmatch('[0-9a-f]{64}', row['sha256']),
                 'valid explicit historical source identity')
            if path in selected and selected[path]['sha256'] != row['sha256']:
                collisions.append(dict(path=path, before=selected[path], after=row,
                                       replacement_manifest_sha256=sha(manifest)))
            selected[path] = {key:row[key] for key in ['path', 'bytes', 'sha256']}
    required = PREFIX+'ramanujan/RESULTS.json'
    need(required in selected, 'include the actual renderer input ramanujan/RESULTS.json explicitly')
    result = []
    destinations = set()
    def add(source, destination, role, expected=None):
        destination = relative(destination)
        need(destination not in destinations, 'duplicate bundle destination: '+destination)
        destinations.add(destination)
        got = checked(source, expected) if expected else identity(source)
        result.append(dict(source=str(source.resolve()), destination=destination, role=role, **got))
    for path in sorted(selected):
        add(args.publication/path, 'publication/'+path, 'Reviewed publication source/evidence', selected[path])
    need(sha(args.analytic/'SOURCE_PACKET.json') == ANALYTIC_SHA,
         'unchanged exact accepted analytic source packet manifest')
    analytic = read(args.analytic/'SOURCE_PACKET.json')
    for key, filename in [('exact_union_manifest_sha256', 'SOURCE_IDENTITIES_739.json'),
            ('actual_validator_read_inventory_sha256', 'READ_DEPENDENCIES_739.json'),
            ('runtime_compatibility_sha256', 'RUNTIME_COMPATIBILITY.json'),
            ('runtime_parent_packet_sha256', 'ORIGINAL_SOURCE_PACKET739_V3.json')]:
        need(sha(args.analytic/filename) == analytic[key], 'pinned analytic companion: '+filename)
    need(len(analytic['files']) == 2577, 'exact immutable analytic2577 packet')
    for row in analytic['files']:
        path = public_path(row['path'])
        add(args.analytic/'source'/path, 'analytic/source/'+path, 'Immutable analytic source packet', row)
    for name in ANALYTIC_OUTER:
        add(args.analytic/name, 'analytic/'+name, 'Immutable analytic packet metadata')
    need(sha(args.finite/'PACKET.json') == FINITE_SHA, 'unchanged exact accepted finite source packet manifest')
    finite = read(args.finite/'PACKET.json')
    need(len(finite['rows']) == 130, 'exact immutable finite130 packet')
    for row in finite['rows']:
        path = public_path(row['path'])
        add(args.finite/path, 'finite/'+path, 'Immutable standalone finite source packet', row)
    for name in ['PACKET.json', 'README.txt']:
        add(args.finite/name, 'finite/'+name, 'Immutable finite packet metadata')
    for label, manifest in [('reports', args.reports_list), ('extra', args.extras_list)]:
        if manifest is None:
            continue
        provenance.append(dict(kind=label, path=str(manifest.resolve()), **identity(manifest)))
        for row in rows(manifest):
            need(type(row.get('source')) is str and Path(row['source']).is_absolute(), 'explicit source required')
            destination = public_path(row['destination'])
            if label == 'reports':
                need(destination.startswith('reports/') and destination.endswith('.html'), 'report HTML destination')
            add(Path(row['source']), destination, row['role'], row)
    args.out.mkdir()
    save(args.out/'SPEC_CANDIDATE_PRIVATE.json', dict(
        status='REVIEW_REQUIRED_EXPLICIT_PUBLICATION_BUNDLE_INPUTS',
        source_commit=args.source_commit,
        scope='Final release candidate; inventory identity only, no new proof-acceptance claim.', files=result))
    save(args.out/'PUBLICATION_SOURCE_INVENTORY.json', dict(
        status='CANDIDATE_SOURCE_ALLOWLIST_REQUIRES_ROOT_REVIEW', source_commit=args.source_commit,
        rows=[selected[path] for path in sorted(selected)], inputs=provenance))
    save(args.out/'COLLISIONS.json', dict(status='EXPLICIT_CHRONOLOGICAL_PUBLICATION_REPLACEMENTS', rows=collisions))
    save(args.out/'RESULT.json', dict(status='PASS_EXACT_CANDIDATE_INPUT_BYTES_NOT_APPROVED',
        source_commit=args.source_commit, files=len(result), publication_files=len(selected),
        bytes=sum(row['bytes'] for row in result), collisions=len(collisions),
        inventory_sha256=sha(args.out/'SPEC_CANDIDATE_PRIVATE.json'), mathematical_acceptance=False))
    print('PASS exact candidate input bytes; Root review still required:', len(result))


if __name__ == '__main__':
    main()
