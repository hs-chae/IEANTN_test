#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: OpenAI (Codex)
"""Bounded read-only association checks for the reproduction portability review.

Checks source identities and the explicit application import inventory. This is
not a Lean proof replay, model trial, namespace fixture, or source/math audit.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile


def need(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    def pairs(items):
        value = {}
        for key, item in items:
            need(key not in value, 'Duplicate JSON key')
            value[key] = item
        return value
    return json.loads(path.read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def sha(path):
    need(path.is_file() and not path.is_symlink(), 'Regular source required: '+str(path))
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for block in iter(lambda: stream.read(2**20), b''):
            digest.update(block)
    return digest.hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--repository', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    root = args.repository.resolve(strict=True)
    study = root/'Solutions/RH080Study.v1'
    need(not os.path.lexists(args.output), 'Fresh review receipt required')
    freeze_path = study/'REPRODUCTION_REVIEW_FREEZE.json'
    frozen = read(freeze_path)
    freeze_files = frozen['files']
    need(len({row['path'] for row in freeze_files}) == len(freeze_files), 'Duplicate frozen source identity')
    for row in freeze_files:
        need(sha(root/row['path']) == row['sha256'], 'Frozen review input changed: '+row['path'])
        need((root/row['path']).stat().st_size == row['bytes'], 'Frozen source byte count changed')
    inventory_path = study/'REPRODUCTION_INPUTS.json'
    inventory = read(inventory_path)
    files = inventory['files']
    need(len({row['path'] for row in files}) == len(files), 'Duplicate reproduction input identity')
    for row in files:
        relative = Path(row['path'])
        need(not relative.is_absolute() and '..' not in relative.parts, 'Invalid repository-relative identity')
        need(sha(root/relative) == row['sha256'], 'Reproduction input changed: '+row['path'])
    # Import only the guarded wrapper definitions, with bytecode disabled.
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('rh080_readonly_review_wrapper', study/'reproduce_study.py')
    wrapper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(wrapper)
    closures = {key: wrapper.source_closure(root, key) for key in wrapper.profiles(root)}
    closure_files = {row['path'] for rows in closures.values() for row in rows}
    need(closure_files <= {row['path'] for row in files}, 'Application import source absent from reproduction inventory')
    mandatory = ['pv', 'canonical', 'cube', 'zero', 'same_source', 'pareto966', 'g80', 'g56']
    mandatory_files = {row['path'] for key in mandatory for row in closures[key]}
    generated_path = study/'GENERATED_CELL_SOURCES.json'
    generated = read(generated_path)['files']
    inventory_by_path = {row['path']: row for row in files}
    need(len(generated) == 49 and len({row['path'] for row in generated}) == 49, 'Generated cell population differs')
    for row in generated:
        need(row['path'] in inventory_by_path, 'Generated cell absent from full input inventory')
        need(row['sha256'] == inventory_by_path[row['path']]['sha256'], 'Generated cell source identity differs')
    runtime = study/'exposure-runtime'
    components_path = runtime/'SOURCE_COMPONENTS.json'
    components = read(components_path)['sources']
    for row in components:
        need(sha(root/row['path']) == row['sha256'], 'Frozen runtime component differs')
    adapter = read(runtime/'ADAPTER_PIN.json')
    for file_key, hash_key in [('adapter_path', 'adapter_sha256'), ('fixture_acceptor_path', 'fixture_acceptor_sha256')]:
        need(sha(root/adapter[file_key]) == adapter[hash_key], 'Frozen gate/acceptor differs')
    references = []
    for path in sorted((runtime/'references').glob('*.json')):
        template = read(path)
        need(sha(root/template['protocol_repository_path']) == template['protocol_sha256'], 'Template protocol differs')
        for row in template['mounts']:
            need(sha(runtime/'references'/row['tree_file']) == row['tree_sha256'], 'Template tree inventory differs')
        references.append(dict(path=str(path.relative_to(root)), sha256=sha(path), mounts=len(template['mounts'])))
    receipt = dict(status='PASS_READ_ONLY_REPRODUCTION_SOURCE_ASSOCIATION_ONLY',
        controller_sha256=sha(Path(__file__)), python_optimization=sys.flags.optimize,
        freeze_sha256=sha(freeze_path), frozen_review_files=len(freeze_files),
        reproduction_inventory_sha256=sha(inventory_path), reproduction_inputs=len(files),
        source_closure_counts={key: len(rows) for key, rows in closures.items()},
        unique_application_lean_sources=len(closure_files), mandatory_profiles=mandatory,
        mandatory_unique_application_lean_sources=len(mandatory_files), all_closures_in_inventory=True,
        materializable_generated_cells=len(generated), generated_manifest_sha256=sha(generated_path),
        runtime_component_manifest_sha256=sha(components_path), runtime_components=len(components),
        public_reference_templates=references, mathematical_proof_replays=0,
        model_inference_calls=0, scope='Source identities, complete explicit current import closure, frozen runtime components and public template/protocol/tree metadata; no application or platform execution acceptance.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix='.review-', dir=args.output.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, 'w') as stream:
            json.dump(receipt, stream, indent=2, allow_nan=False)
            stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
        os.link(temporary, args.output)
    finally:
        temporary.unlink()
    print(json.dumps(dict(status=receipt['status'], inputs=len(files), frozen_files=len(freeze_files))))


if __name__ == '__main__':
    main()
