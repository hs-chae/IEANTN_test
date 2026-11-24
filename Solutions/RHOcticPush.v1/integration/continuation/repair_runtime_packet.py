#!/usr/bin/env python3
"""Add explicitly reviewed runtime inputs and a narrow114-prefix recovery route.

No Lean source or numerical parameter changes. The original packet and default
repository controllers remain immutable; the two Python variants are installed
only in the new packet and are recorded individually in its source manifest.
"""
from pathlib import Path
import argparse, hashlib, json, os

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
PREFIX = 'Solutions/RHOcticPush.v1/'


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False)+'\n')


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--base-packet', type=Path, required=True)
    parser.add_argument('--failed-primary', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    own_sha = sha(__file__)
    base, out = args.base_packet.resolve(), args.out.resolve()
    need(not out.exists() and not out.is_relative_to(base) and not out.is_relative_to(REPO)
         and not out.is_relative_to(args.failed_primary.resolve()), 'fresh separate repaired packet')
    original = json.loads((base/'SOURCE_PACKET.json').read_text())
    need(original['total_proof_modules_with_declared_appends'] == 739, 'exact739 source packet')
    original_rows = {row['path']: row for row in original['files']}
    need(len(original_rows) == original['file_count'], 'unique original file rows')
    entries = list((base/'source').rglob('*'))
    need(not any(path.is_symlink() for path in entries), 'no original packet symlinks')
    need({path.relative_to(base/'source').as_posix() for path in entries if path.is_file()}
         == set(original_rows), 'exact original packet regular-file inventory')
    sources = {}
    for relative, row in original_rows.items():
        path = base/'source'/relative
        need(sha(path) == row['sha256'], 'original immutable source byte identity:'+relative)
        sources[relative] = path
    inventory_path = PREFIX+'integration/continuation/RUNTIME_DEPENDENCIES.json'
    inventory = json.loads((REPO/inventory_path).read_text())
    explicit = {row['path'] for row in inventory['rows']}
    explicit.add(inventory_path)
    explicit.add(PREFIX+'integration/continuation/repair_runtime_packet.py')
    explicit.add(PREFIX+'integration/continuation/restore_original_readers.py')
    for path in (REPO/PREFIX/'integration/runtime_recovery').iterdir():
        need(path.is_file() and not path.is_symlink(), 'regular versioned runtime-recovery input')
        explicit.add(path.relative_to(REPO).as_posix())
    for name in ['runtime-prefix-controls-v1', 'runtime-execution-preflight-v1',
                 'fresh454-runtime-failure-v1']:
        for path in (REPO/PREFIX/'integration/evidence/continuation-20261124'/name).rglob('*'):
            if path.is_file() and not path.is_symlink():
                explicit.add(path.relative_to(REPO).as_posix())
    for row in inventory['rows']:
        need(sha(REPO/row['path']) == row['sha256'], 'reviewed actual runtime input pin')
    for relative in explicit:
        path = REPO/relative
        need(path.is_file() and not path.is_symlink(), 'regular explicit runtime input')
        if relative in sources:
            need(sha(path) == sha(sources[relative]), 'unchanged existing runtime source:'+relative)
        else:
            sources[relative] = path
    variants = []
    for name in ['reproduce.py', 'resume_prefix.py']:
        target = PREFIX+'integration/corrected/'+name
        versioned = PREFIX+'integration/runtime_recovery/'+name
        historical = PREFIX+'integration/runtime_recovery/'+(
            'ORIGINAL_PRIMARY_CONTROLLER.py' if name == 'reproduce.py' else 'ORIGINAL_RESUME_HELPER.py')
        need(sha(sources[target]) == sha(REPO/historical), 'exact preserved old Python controller')
        variants.append({'path': target, 'historical_controller_sha256': sha(sources[target]),
            'installed_controller_sha256': sha(REPO/versioned), 'versioned_source': versioned,
            'reason': 'Precisely scoped same-campaign114-source prefix after missing-runtime-only failure'})
        sources[target] = REPO/versioned
    source = out/'source'
    source.mkdir(parents=True)
    rows = []
    for relative, original_path in sorted(sources.items()):
        parts = Path(relative).parts
        need(not Path(relative).is_absolute() and '..' not in parts
             and not set(parts) & {'.git', '.lake', '__pycache__', 'memory', 'human_input', 'private'}
             and original_path.suffix not in {'.pdf', '.png', '.olean', '.ilean', '.pyc', '.o', '.so'},
             'source publication scope')
        data = original_path.read_bytes()
        data.decode('utf-8')
        target = source/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        rows.append({'path': relative, 'sha256': sha(target), 'bytes': len(data)})
    identities = json.loads((base/'SOURCE_IDENTITIES_739.json').read_text())
    need(len(identities['modules']) == len({row['module'] for row in identities['modules']}) == 739,
         'all739 original unique compiler identities')
    for row in identities['modules']:
        need(sha(source/row['captured_path']) == row['sha256'], 'all739 mathematical/audit sources unchanged')
    for name in ['SOURCE_IDENTITIES_739.json', 'READ_DEPENDENCIES_739.json']:
        (out/name).write_bytes((base/name).read_bytes())
    (out/'ORIGINAL_SOURCE_PACKET739_V3.json').write_bytes((base/'SOURCE_PACKET.json').read_bytes())
    compatibility = {'status': 'EXPLICIT_CONTROLLER_VARIANTS_SEPARATE_OLD_AND_NEW_ACCEPTANCE_SCOPES',
        'old_packet_manifest_sha256': sha(base/'SOURCE_PACKET.json'), 'old_packet': str(base),
        'old_scope': 'The accepted original723/734/Box725/NL737 and7 relocated readbacks require '
            'their original controllers in the preserved old packet. They are not reclassified.',
        'old_reader_reconstruction': 'Run source/Solutions/RHOcticPush.v1/integration/continuation/'
            'restore_original_readers.py --packet REPAIRED_PACKET --out FRESH_RESTORED_PACKET. '
            'It restores all2251 old file hashes using the preserved old manifest and two original '
            'controller files. Every other old source byte is unchanged, so no second23MB source tree '
            'is needed in the archive.',
        'new_scope': 'This packet consistently installs the new primary controller/helper at corrected/. '
            'The unchanged downstream engines bind their new primary receipt to these exact bytes. '
            'The actual114-prefix recovery is explicit; fresh clean reproduction can still omit --resume.',
        'controller_variants': variants, 'all739_Lean_source_hashes_unchanged': True,
        'runtime_inventory_path': inventory_path,
        'runtime_inventory_sha256': sha(source/inventory_path),
        'native_outputs_are_not_unchecked_mathematical_premises': True}
    save(out/'RUNTIME_COMPATIBILITY.json', compatibility)
    result = dict(original)
    result.update({'status': 'REPAIRED_RUNTIME_COMPLETE739_SOURCE_PACKET_NOT_NEW_PROOF_ACCEPTANCE',
        'source_root': str(source), 'file_count': len(rows), 'bytes': sum(row['bytes'] for row in rows),
        'files': rows, 'runtime_parent_packet_sha256': sha(base/'SOURCE_PACKET.json'),
        'runtime_repair_curator_sha256': own_sha, 'runtime_recovery_controller_installed': True,
        'controller_variants': original.get('controller_variants', [])+variants,
        'runtime_compatibility_sha256': sha(out/'RUNTIME_COMPATIBILITY.json')})
    need(sha(__file__) == own_sha, 'runtime packet curator unchanged during execution')
    save(out/'SOURCE_PACKET.json', result)
    print(json.dumps({'status': result['status'], 'files': len(rows), 'bytes': result['bytes'],
                      'unchanged_compiler_module_identities': 739}))


if __name__ == '__main__':
    main()
