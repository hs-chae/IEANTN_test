#!/usr/bin/env python3
"""Actual old-reader compatibility CLIs after exact2251-file reconstruction."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import hashlib, json, os, subprocess, sys, time

D = Path('/data/ivy-rh-octic-20261123')
PACKET = D/'integration/restored-original739-readers-v1'
OUT = D/'integration/restored739-compatibility-readback-v1'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def need(value, message):
    if not value:
        raise ValueError(message)


def main():
    own_sha = sha(__file__)
    need(not OUT.exists(), 'fresh compatibility readback')
    OUT.mkdir()
    (OUT/'coordinator.executed.py').write_bytes(Path(__file__).read_bytes())
    manifest = json.loads((PACKET/'SOURCE_PACKET.json').read_text())
    source = PACKET/'source'
    def inventory():
        entries = list(source.rglob('*'))
        need(not any(path.is_symlink() for path in entries), 'no restored source symlinks')
        need({path.relative_to(source).as_posix() for path in entries if path.is_file()}
             == {row['path'] for row in manifest['files']}, 'exact2251 restored files')
        for row in manifest['files']:
            need(sha(source/row['path']) == row['sha256'], 'exact restored old source hash')
    inventory()
    solution = source/'Solutions/RHOcticPush.v1'
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    env.pop('IEANTN_GENERIC_CONTEXT', None)
    env.pop('LEAN_PATH', None)
    commands = []
    for index, mode in enumerate([[], ['-O'], ['-OO']]):
        commands.append(('preflight-O'+str(index), [sys.executable, '-B', *mode,
            str(solution/'integration/continuation/finish_clean_single_lane.py'), '--check',
            '--source-packet', str(PACKET), '--context',
            str(D/'integration/portable-generic-setup-v2/GENERIC_CONTEXT.json'),
            '--primary', str(OUT/'unused-primary'), '--out', str(OUT/'unused-coordinator')]))
    commands.extend([('box725', [sys.executable, '-B',
        str(solution/'comparisons/reproduce_box_lee.py'), '--verify',
        str(D/'comparison-box-lee-fresh-v2')]), ('nl737', [sys.executable, '-B',
        str(solution/'comparisons/reproduce_nl_parabolic.py'), '--verify',
        str(D/'nl-parabolic-fresh3-v1')])])
    def trial(item):
        label, command = item
        start = time.monotonic()
        process = subprocess.run(command, env=env, capture_output=True, text=True)
        (OUT/(label+'.stdout')).write_text(process.stdout)
        (OUT/(label+'.stderr')).write_text(process.stderr)
        need(process.returncode == 0, 'actual restored-reader CLI:'+label)
        return {'phase': label, 'command': command, 'returncode': process.returncode,
            'seconds': time.monotonic()-start,
            'stdout_sha256': sha(OUT/(label+'.stdout')),
            'stderr_sha256': sha(OUT/(label+'.stderr'))}
    start = time.monotonic()
    rows = [trial(item) for item in commands[:3]]
    with ThreadPoolExecutor(max_workers=2) as pool:
        rows.extend(pool.map(trial, commands[3:]))
    inventory()
    need(sha(__file__) == own_sha, 'unchanged compatibility coordinator')
    result = {'status': 'PASS_RESTORED_OLD2251_READERS_ACTUAL3_MODE_PREFLIGHTS_BOX725_AND_NL737',
        'controller_sha256': own_sha, 'original_packet_manifest_sha256': sha(PACKET/'SOURCE_PACKET.json'),
        'restoration_RESULT_sha256': sha(PACKET/'RESTORATION_RESULT.json'),
        'rows': rows, 'seconds': time.monotonic()-start, 'exact_source_inventory_before_after': True,
        'scope': 'Old accepted evidence readback only; NL recursively validates734 and complete723. '
            'No new theorem compilation or numerical result claimed.'}
    pending = OUT/'.RESULT.pending'
    pending.write_text(json.dumps(result, indent=2)+'\n')
    os.replace(pending, OUT/'RESULT.json')


if __name__ == '__main__':
    main()
