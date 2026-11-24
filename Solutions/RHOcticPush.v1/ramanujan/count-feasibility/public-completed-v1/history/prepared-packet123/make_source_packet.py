#!/usr/bin/env python3
"""Copy the exact, explicitly enumerated clean recipe; never copy proof objects."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil

HERE = Path(__file__).resolve().parent
COUNT = HERE.parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    def pairs(items):
        value = {}
        for key, item in items:
            need(key not in value, 'duplicate JSON key')
            value[key] = item
        return value
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs)


def paths():
    selected = {
        'recover_count.py', 'recover_count_v2.py', 'recovery_origin.py',
        'REGENERATION.json', 'GENERATOR_RESOURCE_VARIANT.json',
        'regeneration/generate_demand_certificate_resources.py',
        'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json',
        'cold-foundation/data_stage.py', 'cold-foundation/source_basis.py',
        'cold-foundation/remaining_stage.py',
        'portable/reproduce.py', 'portable/SOURCE_CLOSURE.json', 'portable/CONTROLLERS.json',
    }
    for parent in ['portable', 'portable-source-run']:
        manifest = read(COUNT/parent/'SOURCE_CLOSURE.json')
        for row in manifest['modules'] + manifest['resources']:
            selected.add(parent+'/source/'+row['relative'])
    for row in read(COUNT/'portable/CONTROLLERS.json')['controllers']:
        selected.add('portable/'+row['path'])
    for name in [
        'reproduce.py', 'readback.py', 'README.md', 'SOURCE_CLOSURE.json',
        'FULL_NUMERICAL_PROFILES.json', 'SOURCE_FREEZE.json', 'make_source_packet.py',
        'test_completed_readback.py', 'EXECUTED_SMOKE.md',
        'SECOND_INDEPENDENT_REVIEW_20261124.json', 'CHECK_PROFILE_CORRIGENDUM.json',
        'ROOT_WRAPPER_READER_INDEPENDENT_REVIEW.json',
        'scripts/reproduce_physical_closure.py',
        'scripts/generate_demand_certificate_resources.py',
        'scripts/ENGINE_SOURCE_FREEZE.json', 'scripts/ROOT_ENGINE_INDEPENDENT_REVIEW.json',
        'scripts/ENGINE_RESOURCE_DIFF.patch', 'scripts/ENGINE_RESOURCE_DIFF_AUDIT.json',
        'scripts/test_physical_resource_gates.py', 'scripts/READMEengine.md',
    ]:
        selected.add('portable-source-run/'+name)
    return sorted(selected)


def build(out):
    out = out.resolve()
    need(not out.exists() and out.parent.is_dir(), 'fresh packet directory')
    need(not out.is_relative_to(COUNT), 'packet outside source directory')
    target = out/'project/Solutions/RHOcticPush.v1/ramanujan/count-feasibility'
    rows = []
    for relative in paths():
        source = COUNT/relative
        need(source.is_file() and not source.is_symlink() and
             source.resolve().is_relative_to(COUNT), 'owned exact packet source')
        need(source.suffix not in {'.olean', '.ilean', '.so', '.a', '.o'},
             'source only, never an application object')
        destination = target/relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        need(sha(destination) == sha(source), 'exact packet copy')
        rows.append(dict(path=str(destination.relative_to(out)), sha256=sha(source),
                         bytes=source.stat().st_size))
    receipt = dict(schema='RH_COUNT_SOURCE_ONLY_PACKET_V1',
        script_sha256=sha(__file__), rows=rows, total_bytes=sum(q['bytes'] for q in rows),
        application_proof_objects_included=False,
        numerical_data_included=False,
        execution='Use portable-source-run/reproduce.py with an actual generic-only context.',
        proof_scope='Source packet creation is not numerical verification; actual run receipts are separate.')
    (out/'PACKET.json').write_text(json.dumps(receipt, indent=2, allow_nan=False)+'\n')
    (out/'README.txt').write_text(
        'This packet contains source, exact dependency/recipe pins, and reviewed controllers.\n'
        'No application proof object or numerical certificate is an input.\n'
        'From project/, run the command in\n'
        'Solutions/RHOcticPush.v1/ramanujan/count-feasibility/portable-source-run/README.md.\n'
        'Supply an actual pinned GENERIC_CONTEXT.json containing only generic libraries.\n'
        'The bounded --smoke mode proves pi(1000)=168 plus the parameterized high-source model.\n'
        'Only the full mode proves the fixed high-output count.\n')
    return receipt


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    receipt = build(args.out)
    print('SOURCE_ONLY_PACKET', len(receipt['rows']), receipt['total_bytes'])


if __name__ == '__main__':
    main()
