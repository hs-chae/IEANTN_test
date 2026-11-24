#!/usr/bin/env python3
"""Restore the byte-exact historical reader packet from preserved source bytes.

Use the restored packet for original accepted-run readbacks. Use the repaired
packet for a new complete clean reproduction or the explicit114-source recovery.
"""
from pathlib import Path
import argparse, hashlib, json, shutil


def need(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    packet, out = args.packet.resolve(), args.out.resolve()
    need(not out.exists() and not out.is_relative_to(packet), 'fresh separate historical reader packet')
    new = json.loads((packet/'SOURCE_PACKET.json').read_text())
    historical = packet/'ORIGINAL_SOURCE_PACKET739_V3.json'
    need(sha(historical) == new['runtime_parent_packet_sha256'], 'exact original packet manifest')
    old = json.loads(historical.read_text())
    source = packet/'source'
    originals = {
        'Solutions/RHOcticPush.v1/integration/corrected/reproduce.py':
            'Solutions/RHOcticPush.v1/integration/runtime_recovery/ORIGINAL_PRIMARY_CONTROLLER.py',
        'Solutions/RHOcticPush.v1/integration/corrected/resume_prefix.py':
            'Solutions/RHOcticPush.v1/integration/runtime_recovery/ORIGINAL_RESUME_HELPER.py'}
    need(len(old['files']) == old['file_count'] == 2251
         == len({row['path'] for row in old['files']}), 'unique complete original file inventory')
    selected = []
    for row in old['files']:
        relative = Path(row['path'])
        need(not relative.is_absolute() and '..' not in relative.parts, 'historical relative source path')
        original = source/originals.get(row['path'], row['path'])
        need(original.is_file() and not original.is_symlink()
             and original.resolve().is_relative_to(source)
             and sha(original) == row['sha256'], 'retained exact historical source:'+row['path'])
        selected.append((row, original))
    target_source = out/'source'
    target_source.mkdir(parents=True)
    for row, original in selected:
        target = target_source/row['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(original, target)
        need(sha(target) == row['sha256'], 'restored exact historical source')
    shutil.copyfile(historical, out/'SOURCE_PACKET.json')
    for name in ['SOURCE_IDENTITIES_739.json', 'READ_DEPENDENCIES_739.json']:
        shutil.copyfile(packet/name, out/name)
    result = {'status': 'PASS_EXACT_ORIGINAL2251_FILE_READER_PACKET_RESTORED',
        'historical_packet_manifest_sha256': sha(out/'SOURCE_PACKET.json'),
        'repaired_packet_manifest_sha256': sha(packet/'SOURCE_PACKET.json'),
        'source_files': len(selected), 'source_bytes': sum(row['bytes'] for row, _original in selected),
        'qualification': 'Historical scoped accepted-run reader only; original missing-runtime '
            'packaging failure is preserved. Fresh full reproduction uses the repaired packet.'}
    (out/'RESTORATION_RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'])


if __name__ == '__main__':
    main()
