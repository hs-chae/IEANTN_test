#!/usr/bin/env python3
"""Export the frozen712 or723 proof closure and clean reproduction routes.

The historical619 exporter/packets remain unchanged. This is a source export,
not a verification receipt. Its explicit controller variant can recover only
the preserved80-module clean prefix after the recorded generic-cache failure.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil

I = Path(__file__).resolve().parent
R = I.parents[2]

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

MANIFESTS = ['Solutions/RHLimit.v1/'+part+'/SOURCE_CLOSURE.json'
             for part in ['pi', 'spectral', 'integration']]+[
    'Solutions/RHOcticPush.v1/integration/corrected/capture/SOURCE_CLOSURE.json',
    'Solutions/RHOcticPush.v1/integration/supplement/audit-corrected-capture/SOURCE_CLOSURE.json',
    'Solutions/RHOcticPush.v1/box/zero/cold-capture/SOURCE_CLOSURE.json',
    'Solutions/RHOcticPush.v1/integration/closed_box/capture/SOURCE_CLOSURE.json',
    'Solutions/RHOcticPush.v1/integration/spectral_final/capture/SOURCE_CLOSURE.json']

def check(root, include_ram606=False):
    identities = {}
    manifests = MANIFESTS+([
        'Solutions/RHOcticPush.v1/integration/ram606/capture/SOURCE_CLOSURE.json']
        if include_ram606 else [])
    for rel in manifests:
        manifest = json.loads((root/rel).read_text())
        for row in manifest['modules']:
            need(row['module'] not in identities, 'duplicate compiler module identity')
            need(sha(root/row['path']) == row['sha256'],
                 'packet frozen proof source drift:'+row['module'])
            if row.get('original_path') is not None:
                need(sha(root/row['original_path']) == row['sha256'],
                     'packet author proof source drift:'+row['module'])
            identities[row['module']] = row['sha256']
        for resource in manifest.get('resources', []):
            need(sha(root/resource['path']) == resource['sha256'], 'included payload identity')
    need(len(identities) == (723 if include_ram606 else 712),
         'complete exact selected source universe')
    return identities

def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--with-clean-recovery', action='store_true')
    parser.add_argument('--include-ram606', action='store_true')
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists() and not out.is_relative_to(R), 'fresh packet outside checkout')
    expected = check(R, args.include_ram606)
    source = out/'source'
    source.mkdir(parents=True)
    extensions = {'.lean', '.py', '.json', '.yaml', '.yml', '.toml', '.c', '.cpp', '.cu',
                  '.h', '.hpp', '.md', '.txt', '.csv', '.sh', '.in', '.lock', '.pdf', '.html'}
    for directory, subdirs, files in os.walk(R):
        subdirs[:] = sorted(x for x in subdirs
                            if x not in {'.git', '.lake', '__pycache__', 'node_modules'}
                            and not (Path(directory)/x).is_symlink())
        for name in sorted(files):
            path = Path(directory)/name
            if path.is_symlink() or not (path.suffix in extensions
                                         or name in {'lean-toolchain', 'LICENSE'}):
                continue
            target = source/path.relative_to(R)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, target)
    # Install only the separately versioned primary controller/helper. The
    # immutable mathematical captures and every proof source remain unchanged.
    integration = source/'Solutions/RHOcticPush.v1/integration'
    replacements = []
    for filename in (['reproduce.py', 'resume_prefix.py'] if args.with_clean_recovery else []):
        original = integration/'corrected'/filename
        previous = sha(original)
        replacement = integration/'clean_recovery'/filename
        original.write_bytes(replacement.read_bytes())
        replacements.append({'path': str(original.relative_to(source)),
                             'historical_controller_sha256': previous,
                             'installed_controller_sha256': sha(original),
                             'versioned_source': str(replacement.relative_to(source))})
    need(check(source, args.include_ram606) == expected, 'relocated complete proof source identity')
    rows = []
    for path in sorted(source.rglob('*')):
        if path.is_file():
            need(not path.is_symlink(), 'no source packet symlinks')
            rows.append({'path': str(path.relative_to(source)), 'sha256': sha(path),
                         'bytes': path.stat().st_size})
    result = {'status': 'SOURCE_ONLY_EXPORT_NOT_PROOF_ACCEPTANCE',
              'schema': 'RH723_PACKET_V1' if args.include_ram606 else 'RH712_PACKET_V1',
              'source_root': str(source), 'file_count': len(rows),
              'bytes': sum(row['bytes'] for row in rows), 'exact_proof_modules': len(expected),
              'proof_universe': expected, 'controller_variants': replacements,
              'clean_recovery_controller_installed': args.with_clean_recovery,
              'source_controller_sha256': sha(__file__),
              'excluded': ['.git', '.lake', 'symlinks', 'compiled proof objects',
                           'executable binaries', 'application proof caches'],
              'generic_requirements': 'Pinned generic source commits and compiler remain external; '
                                      'complete all selected generic prerequisites before the run.',
              'publication_scope': 'This broad local reproduction snapshot retains historical text. '
                                   'Only the selected frozen proof universe is claimed; public '
                                   'delivery must use the reviewed publication scope.',
              'trust': 'Kernel mathematics with explicit general published source inputs. '
                       'No official Comparator receipt or source-first PV claim.', 'files': rows}
    candidate = out/'SOURCE_PACKET.pending.json'
    candidate.write_text(json.dumps(result, indent=2)+'\n')
    os.replace(candidate, out/'SOURCE_PACKET.json')
    print(json.dumps({key: result[key] for key in
                      ['status', 'file_count', 'bytes', 'exact_proof_modules']}))

if __name__ == '__main__':
    main()
