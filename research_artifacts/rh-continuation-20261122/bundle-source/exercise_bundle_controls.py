#!/usr/bin/env python3
"""Actual bundle-selector/archive CLIs in all Python optimization modes."""
from pathlib import Path
import argparse, io, json, os, subprocess, sys, tarfile

def need(ok, message):
    if not ok:
        raise ValueError(message)

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--tool', type=Path, required=True)
    p.add_argument('--network', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    a = p.parse_args(); need(not a.out.exists(), 'fresh controls output required')
    a.out.mkdir(parents=True); results = []
    def run(mode, label, args, good):
        flags = [] if mode == 0 else ['-O'] if mode == 1 else ['-OO']
        command = [sys.executable, *flags, str(a.tool.resolve()), *args]
        r = subprocess.run(command, text=True, capture_output=True)
        row = {'mode': mode, 'label': label, 'command': command, 'returncode': r.returncode,
               'expected_success': good, 'stdout': r.stdout, 'stderr': r.stderr}
        results.append(row)
        (a.out / 'PARTIAL.json').write_text(json.dumps(results, indent=2) + '\n')
        need((r.returncode == 0) == good, 'unexpected CLI result: ' + label)
    for mode in [0, 1, 2]:
        root = a.out / ('mode-' + str(mode)); root.mkdir()
        stage = root / 'selected-source'
        run(mode, 'stage-real-source', ['stage', '--network', str(a.network.resolve()), '--out', str(stage)], True)
        fixture = root / 'fixture'; fixture.mkdir(); (fixture / 'payload.txt').write_text('source identity\n')
        run(mode, 'seal', ['seal', '--tree', str(fixture)], True)
        run(mode, 'verify', ['verify', '--tree', str(fixture)], True)
        archive = root / 'valid.tar.gz'
        run(mode, 'pack', ['pack', '--tree', str(fixture), '--out', str(archive)], True)
        run(mode, 'extract', ['extract', '--archive', str(archive), '--out', str(root / 'extracted')], True)
        run(mode, 'reject-archive-inside-tree', ['pack', '--tree', str(fixture), '--out', str(fixture / 'inside.tar.gz')], False)
        run(mode, 'reject-existing-archive', ['pack', '--tree', str(fixture), '--out', str(archive)], False)
        run(mode, 'reject-existing-extraction', ['extract', '--archive', str(archive), '--out', str(root / 'extracted')], False)
        (fixture / 'payload.txt').write_text('corrupted\n')
        run(mode, 'reject-corrupted-payload', ['verify', '--tree', str(fixture)], False)
        (fixture / 'payload.txt').write_text('source identity\n')
        (fixture / 'extra.txt').write_text('unmanifested\n')
        run(mode, 'reject-unmanifested-extra', ['verify', '--tree', str(fixture)], False)
        manifest = root / 'bad-manifest'; manifest.mkdir()
        (manifest / 'BUNDLE_MANIFEST.json').write_text('{"schema":"x","schema":"STRICT_RELATIVE_FILE_HASH_MANIFEST_V1","files":[]}')
        run(mode, 'reject-duplicate-JSON-key', ['verify', '--tree', str(manifest)], False)
        (manifest / 'BUNDLE_MANIFEST.json').write_text('{"schema":"STRICT_RELATIVE_FILE_HASH_MANIFEST_V1","files":[],"extra":1e999}')
        run(mode, 'reject-overflowing-JSON-float', ['verify', '--tree', str(manifest)], False)
        attacks = {
            'traversal': [('../escape', 'file')], 'absolute': [('/escape', 'file')],
            'backslash': [('dir\\escape', 'file')], 'duplicate': [('same', 'file'), ('same', 'file')],
            'symlink': [('link', 'link')], 'prefix': [('file', 'file'), ('file/child', 'file')],
            'dot-component': [('dir/../escape', 'file')],
        }
        for label, members in attacks.items():
            bad = root / (label + '.tar.gz')
            with tarfile.open(bad, 'w:gz') as tf:
                content = b'{}'
                info = tarfile.TarInfo('BUNDLE_MANIFEST.json'); info.size = len(content)
                tf.addfile(info, io.BytesIO(content))
                for name, kind in members:
                    info = tarfile.TarInfo(name)
                    if kind == 'link':
                        info.type = tarfile.SYMTYPE; info.linkname = '/tmp/escape'; tf.addfile(info)
                    else:
                        info.size = len(content); tf.addfile(info, io.BytesIO(content))
            dest = root / ('reject-' + label)
            run(mode, 'reject-' + label, ['extract', '--archive', str(bad), '--out', str(dest)], False)
            need(not dest.exists(), 'unsafe archive wrote before full membership validation: ' + label)
        for action in ['stage', 'seal', 'verify', 'pack', 'extract']:
            run(mode, 'reject-missing-arguments-' + action, [action], False)
            run(mode, 'reject-unknown-argument-' + action, [action, '--unexpected'], False)
    result = {'schema': 'STRICT_BUNDLE_ACTUAL_CLI_CONTROLS_V1', 'status': 'PASS_ALL_ACTUAL_CLIS_NORMAL_O_OO',
              'cases': len(results), 'modes': [0, 1, 2], 'results': results}
    temporary = a.out / 'RESULT.pending'; temporary.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(temporary, a.out / 'RESULT.json'); print(json.dumps({'status': result['status'], 'cases': len(results)}))

if __name__ == '__main__':
    main()
