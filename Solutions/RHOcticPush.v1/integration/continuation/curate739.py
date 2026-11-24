#!/usr/bin/env python3
"""Export the exact overlapping723+11+2+3 source closure, without object caches.

Actual accepted validators supply a file-read inventory. Compiler identities are
independently joined from all frozen manifests and actual comparison sources.
This export is not a new mathematical acceptance receipt or a provenance census.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import math
import os
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PREFIX = 'Solutions/RHOcticPush.v1/'


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON key:'+key)
            result[key] = value
        return result
    def finite(value):
        number = float(value)
        need(math.isfinite(number), 'nonfinite JSON number')
        return number
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs, parse_float=finite,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite JSON')))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def save(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--base-packet', type=Path, required=True)
    parser.add_argument('--accepted734', type=Path, required=True)
    parser.add_argument('--accepted-box', type=Path, required=True)
    parser.add_argument('--accepted-nl', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    controller_sha = sha(__file__)
    base, out = args.base_packet.resolve(), args.out.resolve()
    need(not out.exists() and not out.is_relative_to(REPO)
         and not out.is_relative_to(base), 'fresh separate source export')
    for accepted_root in [args.accepted734, args.accepted_box, args.accepted_nl]:
        need(not out.is_relative_to(accepted_root.resolve()),
             'source export must be separate from every accepted proof run')
    original = read(base/'SOURCE_PACKET.json')
    need(original['schema'] == 'RH723_PACKET_V1'
         and type(original['exact_proof_modules']) is int
         and original['exact_proof_modules'] == 723, 'exact723 base source packet')
    opened = set()

    def hook(event, arguments):
        if event != 'open' or not arguments or not isinstance(arguments[0], (str, bytes)):
            return
        try:
            path = Path(os.fsdecode(arguments[0])).resolve()
            if path.suffix == '.pyc' and '__pycache__' in path.parts:
                path = Path(importlib.util.source_from_cache(str(path)))
            if path.is_relative_to(REPO) and path.is_file():
                if '.lake' not in path.relative_to(REPO).parts:
                    opened.add(path.relative_to(REPO).as_posix())
        except (OSError, ValueError):
            return

    sys.addaudithook(hook)
    feedback = load('public739feedback', REPO/PREFIX/'integration/feedback/reproduce.py')
    box = load('public739box', REPO/PREFIX/'comparisons/reproduce_box_lee.py')
    nl = load('public739nl', REPO/PREFIX/'comparisons/reproduce_nl_parabolic.py')
    accepted = {
        'feedback734': (feedback.validate(args.accepted734), args.accepted734),
        'box725': (box.validate(args.accepted_box), args.accepted_box),
        'nl737': (nl.validate(args.accepted_nl), args.accepted_nl),
    }
    need([row[0]['total_source_modules'] for row in accepted.values()] == [734, 725, 737],
         'actual complete scoped accepted sources')
    exporter = load('public739base', REPO/PREFIX/'integration/prepare_complete_source_packet.py')
    need(exporter.check(REPO, include_ram606=True) == original['proof_universe'],
         'all723 immutable compiler source identities')
    manifests = exporter.MANIFESTS+[
        PREFIX+'integration/ram606/capture/SOURCE_CLOSURE.json',
        PREFIX+'integration/feedback/capture/SOURCE_CLOSURE.json']
    explicit = set()
    identities = {}
    resources = {}
    for relative in manifests:
        manifest = read(REPO/relative)
        explicit.add(relative)
        for row in manifest['modules']:
            name = row['module']
            need(name not in identities, 'duplicate compiler module identity:'+name)
            need(sha(REPO/row['path']) == row['sha256'], 'captured source:'+name)
            paths = [row['path']]
            if row.get('original_path') is not None:
                need(sha(REPO/row['original_path']) == row['sha256'], 'author source:'+name)
                paths.append(row['original_path'])
            explicit.update(paths)
            identities[name] = {'module': name, 'sha256': row['sha256'],
                'captured_path': row['path'], 'matching_source_paths': paths,
                'frozen_manifest': relative}
        for row in manifest.get('resources', []):
            need(sha(REPO/row['path']) == row['sha256'], 'exact C/include resource')
            explicit.add(row['path'])
            if row['path'] in resources:
                need(resources[row['path']]['sha256'] == row['sha256'], 'resource identity collision')
                resources[row['path']]['manifests'].append(relative)
            else:
                resources[row['path']] = {'path': row['path'], 'sha256': row['sha256'],
                                          'manifests': [relative]}
    need(len(identities) == 734, 'exact723 plus11 frozen sources')
    for family, engine, run in [('box', box, args.accepted_box), ('nl', nl, args.accepted_nl)]:
        for row in read(run/'RESULT.json')['compilations']:
            name = row['module']
            relative = PREFIX+'comparisons/'+name+'.lean'
            need(name not in identities and sha(REPO/relative) == row['source_sha256']
                 == sha(run/'source'/(name+'.lean')), 'actual unique comparison source:'+name)
            if family == 'box' and name == 'BoxLeeAudit':
                need((REPO/relative).read_text() == engine.AUDIT, 'renderer audit source identity')
            identities[name] = {'module': name, 'sha256': row['source_sha256'],
                'captured_path': relative, 'matching_source_paths': [relative],
                'actual_compilation_receipt_sha256': sha(run/'RESULT.json'),
                'scope': family+' source append, existing basis overlaps other scoped results'}
            explicit.add(relative)
    need(len(identities) == 739, 'exact unique analytic compiler identity union')
    feedback_manifest = feedback.manifest_check(
        REPO/PREFIX/'integration/feedback/capture/SOURCE_CLOSURE.json')
    for row in feedback_manifest['freezes']+feedback_manifest['canonical_metadata']:
        explicit.add(row['path'])
    explicit.add(feedback_manifest['exact_type_inventory']['path'])
    for folder in ['IEANTN/Nodes/RHPrimeCounting/v6', 'Solutions/RHPrimeCounting.v6']:
        explicit.update(path.relative_to(REPO).as_posix() for path in (REPO/folder).iterdir()
                        if path.is_file() and not path.is_symlink())
    nl_allowlist = REPO/PREFIX/'comparisons/NL_PARABOLIC_PUBLIC_FILES.json'
    nl_public = read(nl_allowlist)
    need(type(nl_public['files']) is int and len(nl_public['rows']) == nl_public['files'],
         'complete NL public supplement rows')
    for row in nl_public['rows']:
        path = REPO/row['path']
        need(path.is_file() and not path.is_symlink() and sha(path) == row['sha256']
             and path.stat().st_size == row['bytes'], 'frozen NL public input:'+row['path'])
        explicit.add(row['path'])
    explicit.add(nl_allowlist.relative_to(REPO).as_posix())
    for name in ['README.md', 'requirements.txt', 'regenerate_moments.py',
                 'finish_clean_single_lane.py', 'RESOURCE_VARIANT.json',
                 'bootstrap_generic.py', 'COMPACT739_PLAN.json', 'curate739.py']:
        explicit.add(PREFIX+'integration/continuation/'+name)
    for name in ['ENDPOINT_PROPOSALS.json', 'LOG_PROPOSALS.json', 'CELL_PROPOSALS.json']:
        explicit.add(PREFIX+'moments/endpoint/'+name)
    for name in ['reproduce.py', 'prepare.py', 'controls.py', 'CONTROLS_COMPLETION.json',
                 'CONTROLS_ROOT_INDEPENDENT_REVIEW.json', 'EXACT_TYPES.json']:
        explicit.add(PREFIX+'integration/feedback/'+name)
    for name in ['reproduce_box_lee.py', 'test_box_lee.py', 'BOX_LEE_SOURCE_FREEZE.json',
                 'BOX_LEE_REPRODUCER_FREEZE.json', 'BOX_LEE_COMPLETION.json',
                 'BOX_LEE_INDEPENDENT_REVIEW.json', 'BOX_LEE_CONTROLLER_REVIEW.json',
                 'BOX_LEE_CONTROL_CORRIGENDUM.json']:
        explicit.add(PREFIX+'comparisons/'+name)
    for folder in [PREFIX+'integration/feedback/evidence/fresh11-v1',
                   PREFIX+'integration/feedback/evidence/controls69-v2',
                   PREFIX+'integration/evidence/continuation-20261124',
                   PREFIX+'comparisons/evidence/box-lee-controls-v3']:
        explicit.update(path.relative_to(REPO).as_posix() for path in (REPO/folder).rglob('*')
                        if path.is_file() and not path.is_symlink())
    sources = {}
    for row in original['files']:
        relative = row['path']
        path = base/'source'/relative
        need(path.is_file() and not path.is_symlink() and sha(path) == row['sha256'],
             'base frozen regular source:'+relative)
        sources[relative] = path
    for relative in opened | explicit:
        path = REPO/relative
        need(path.is_file() and not path.is_symlink(), 'actual additional regular input:'+relative)
        if relative in sources:
            need(sha(path) == sha(sources[relative]), 'existing723 source changed:'+relative)
        else:
            sources[relative] = path
    source = out/'source'
    source.mkdir(parents=True)
    forbidden = {'.git', '.lake', '__pycache__', 'node_modules', 'memory', 'human_input',
                 'private', 'transcripts'}
    banned = {'.pdf', '.png', '.jpg', '.olean', '.ilean', '.pyc', '.o', '.so', '.a', '.exe'}
    rows = []
    for relative, path in sorted(sources.items()):
        parts = Path(relative).parts
        need(not Path(relative).is_absolute() and '..' not in parts
             and not (set(parts) & forbidden) and path.suffix not in banned,
             'publication scope exclusion:'+relative)
        data = path.read_bytes()
        data.decode('utf-8')
        target = source/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        rows.append({'path': relative, 'sha256': sha(target), 'bytes': len(data)})
    need(exporter.check(source, include_ram606=True) == original['proof_universe'],
         'relocated723 source identities')
    for row in identities.values():
        need(sha(source/row['captured_path']) == row['sha256'], 'relocated739 source identity')
    inventory = {'status': 'ACTUAL_SCOPED_VALIDATOR_SOURCE_READ_INVENTORY_NOT_PROVENANCE_CENSUS',
        'paths': sorted(opened), 'explicit_reproduction_additions': sorted(explicit),
        'accepted_scoped_results': {name: {'root': str(root.resolve()),
            'RESULT_sha256': sha(root/'RESULT.json')} for name, (_receipt, root) in accepted.items()}}
    save(out/'READ_DEPENDENCIES_739.json', inventory)
    identity_result = {'status': 'EXACT739_UNIQUE_COMPILER_IDENTITIES_NOT739_NEW_THEOREMS',
        'composition': {'base': 723, 'feedback_append': 11, 'box_lee_append': 2, 'nl_append': 3},
        'scoped_closure_sizes_not_disjoint': [723, 734, 725, 737],
        'modules': [identities[name] for name in sorted(identities)],
        'C_and_include_resources': [resources[name] for name in sorted(resources)],
        'claim': 'Source identity union only. Every scoped acceptance and trust boundary remains separate.'}
    save(out/'SOURCE_IDENTITIES_739.json', identity_result)
    need(sha(__file__) == controller_sha, 'curator unchanged during execution')
    result = dict(original)
    result.update({'status': 'CURATED_SOURCE_EXPORT_EXACT739_UNION_NOT_NEW_PROOF_ACCEPTANCE',
        'base_packet_manifest_sha256': sha(base/'SOURCE_PACKET.json'),
        'file_count': len(rows), 'bytes': sum(row['bytes'] for row in rows), 'files': rows,
        'source_root': str(source), 'curator739_sha256': controller_sha,
        'total_proof_modules_with_declared_appends': 739,
        'declared_append_composition': identity_result['composition'],
        'exact_union_manifest_sha256': sha(out/'SOURCE_IDENTITIES_739.json'),
        'actual_validator_read_inventory_sha256': sha(out/'READ_DEPENDENCIES_739.json'),
        'base_schema_scope': 'Unchanged base coordinator builds723; feedback adds11, Box adds2 '
                            'above723, NL adds3 above734. These scoped closures overlap.',
        'publication_scope': 'Exact selected application source, complete reproducibility inputs '
            'and concise scoped evidence. No broad historical snapshot, private context, primary '
            'PDF, application object cache or compiled artifact.'})
    save(out/'SOURCE_PACKET.json', result)
    print(json.dumps({'status': result['status'], 'files': len(rows), 'bytes': result['bytes'],
                      'unique_compiler_modules': len(identities)}))


if __name__ == '__main__':
    main()
