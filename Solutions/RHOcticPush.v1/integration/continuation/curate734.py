#!/usr/bin/env python3
"""Extend the exact public723 packet with the frozen734 source append.

Every existing source byte is preserved. New selection consists of the actual
strict734 validator's file-read dependency inventory, all eleven manifest source
identities and explicit reproduction/interface inputs. No old application object
bank, broad historical snapshot, private context or primary PDF is exported.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--base-packet', type=Path, required=True)
    parser.add_argument('--accepted734', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    base, out = args.base_packet.resolve(), args.out.resolve()
    need(not out.exists() and not out.is_relative_to(REPO)
         and not out.is_relative_to(base), 'fresh separate source export')
    original = json.loads((base/'SOURCE_PACKET.json').read_text())
    need(original['schema'] == 'RH723_PACKET_V1' and original['exact_proof_modules'] == 723,
         'exact723 base source packet')
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
    controller = REPO/'Solutions/RHOcticPush.v1/integration/feedback/reproduce.py'
    validator = load('curated734validator', controller)
    accepted = validator.validate(args.accepted734)
    need(accepted['total_source_modules'] == 734, 'actual validated734 source closure')
    manifest_path = REPO/'Solutions/RHOcticPush.v1/integration/feedback/capture/SOURCE_CLOSURE.json'
    manifest = validator.manifest_check(manifest_path)
    explicit = {
        'Solutions/RHOcticPush.v1/integration/feedback/reproduce.py',
        'Solutions/RHOcticPush.v1/integration/feedback/prepare.py',
        'Solutions/RHOcticPush.v1/integration/feedback/controls.py',
        'Solutions/RHOcticPush.v1/integration/feedback/capture/SOURCE_CLOSURE.json',
        'Solutions/RHOcticPush.v1/integration/feedback/EXACT_TYPES.json',
        'Solutions/RHOcticPush.v1/integration/continuation/finish_clean_single_lane.py',
        'Solutions/RHOcticPush.v1/integration/continuation/RESOURCE_VARIANT.json',
        'Solutions/RHOcticPush.v1/integration/continuation/bootstrap_generic.py',
        str(Path(__file__).resolve().relative_to(REPO)),
        'Solutions/RHOcticPush.v1/comparisons/BoxVsLee.lean',
        'Solutions/RHOcticPush.v1/comparisons/BOX_LEE_SOURCE_FREEZE.json',
        'Solutions/RHOcticPush.v1/comparisons/reproduce_box_lee.py',
        'Solutions/RHOcticPush.v1/comparisons/test_box_lee.py',
        'Solutions/RHOcticPush.v1/comparisons/BOX_LEE_REPRODUCER_FREEZE.json',
        'Solutions/RHOcticPush.v1/comparisons/BOX_LEE_COMPLETION.json',
        'Solutions/RHOcticPush.v1/comparisons/BOX_LEE_INDEPENDENT_REVIEW.json',
        'Solutions/RHOcticPush.v1/comparisons/BOX_LEE_CONTROLLER_REVIEW.json',
    }
    for module in manifest['modules']:
        explicit.add(module['path'])
        if module.get('original_path') is not None:
            explicit.add(module['original_path'])
    for row in manifest['freezes']+manifest['canonical_metadata']:
        explicit.add(row['path'])
    explicit.add(manifest['exact_type_inventory']['path'])
    for folder in ['IEANTN/Nodes/RHPrimeCounting/v6', 'Solutions/RHPrimeCounting.v6']:
        for path in (REPO/folder).iterdir():
            if path.is_file() and not path.is_symlink():
                explicit.add(path.relative_to(REPO).as_posix())
    # Small immutable compiler receipts/logs explain the source-fresh append.
    evidence = REPO/'Solutions/RHOcticPush.v1/integration/feedback/evidence/fresh11-v1'
    explicit.update(path.relative_to(REPO).as_posix() for path in evidence.rglob('*')
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
    exporter = load('curated734baseexporter',
                    source/'Solutions/RHOcticPush.v1/integration/prepare_complete_source_packet.py')
    need(exporter.check(source, include_ram606=True) == original['proof_universe'],
         'all723 immutable compiler source identities')
    new_controller = load('curated734sourcevalidator',
                          source/'Solutions/RHOcticPush.v1/integration/feedback/reproduce.py')
    need(new_controller.manifest_check(
        source/'Solutions/RHOcticPush.v1/integration/feedback/capture/SOURCE_CLOSURE.json') == manifest,
        'all eleven additional source identities and actual contracts')
    inventory = {'status': 'ACTUAL_734_VALIDATOR_SOURCE_READ_INVENTORY_NOT_PROVENANCE_CENSUS',
        'paths': sorted(opened), 'explicit_reproduction_additions': sorted(explicit),
        'accepted_run_RESULT_sha256': sha(args.accepted734/'RESULT.json')}
    (out/'READ_DEPENDENCIES_734.json').write_text(json.dumps(inventory, indent=2)+'\n')
    result = dict(original)
    result.update({'status': 'CURATED_SOURCE_EXPORT_WITH_FROZEN734_APPEND_NOT_NEW_PROOF_ACCEPTANCE',
        'base_packet_manifest_sha256': sha(base/'SOURCE_PACKET.json'),
        'file_count': len(rows), 'bytes': sum(row['bytes'] for row in rows), 'files': rows,
        'source_root': str(source), 'curator734_sha256': sha(__file__),
        'additional_scientific_manifest': 'Solutions/RHOcticPush.v1/integration/feedback/capture/SOURCE_CLOSURE.json',
        'additional_source_modules': 11, 'total_proof_modules_with_declared_append': 734,
        'actual_validator_read_inventory_sha256': sha(out/'READ_DEPENDENCIES_734.json'),
        'base_schema_scope': 'The unmodified base coordinator verifies723. The separate feedback '
            'controller compiles eleven actual sources above that accepted basis. Source sets are '
            'overlapping and are not added as unrelated totals.',
        'publication_scope': 'Exact selected723 base, frozen734 append and necessary explicit '
            'reproduction/interface inputs only; no broad historical text, private context, primary '
            'PDF, application object cache or compiled artifact.'})
    pending = out/'SOURCE_PACKET.pending.json'
    pending.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    os.replace(pending, out/'SOURCE_PACKET.json')
    print(json.dumps({'status': result['status'], 'files': len(rows), 'bytes': result['bytes']}))


if __name__ == '__main__':
    main()
