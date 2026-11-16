"""Exercise actual prepared4057-source CLIs in normal, -O and -OO modes."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

B = Path(__file__).resolve().parent

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents, 'fresh controls outside capsule')
    out.mkdir(parents=True)
    records = []
    start = time.monotonic()
    def run(name, command, accept):
        with (out / (name + '.stdout')).open('wb') as f, (out / (name + '.stderr')).open('wb') as g:
            q = subprocess.run(command, stdout=f, stderr=g)
        need((q.returncode == 0) == accept, 'unexpected control result: ' + name)
        records.append(dict(name=name, command=command, exit_code=q.returncode,
            expected_accept=accept, stdout_sha256=sha(out / (name + '.stdout')),
            stderr_sha256=sha(out / (name + '.stderr'))))
    for label, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        command = [sys.executable, *flags, str(B / 'reproduce.py')]
        positive = out / (label + '-identity')
        run(label + '-identity', command + ['--out', str(positive), '--check-source-only'], True)
        receipt = json.loads((positive / 'RECEIPT.json').read_text())
        need(receipt['status'] == 'PASS4057_SOURCE_IDENTITIES_ONLY_NOT_REPLAY'
             and receipt['source_modules'] == 4057 and receipt['theorem_roots'] == 12234
             and receipt['proof_replay_completed'] is False, 'identity-only honest acceptance')
        failures = [('--jobs', '0'), ('--jobs', '17'), ('--point-jobs', '0'),
                    ('--frame-jobs', '17'), ('--edge-jobs', '17'), ('--cell-jobs', '17'),
                    ('--weight-jobs', '17'), ('--slope-jobs', '17')]
        for number, extra in enumerate(failures):
            run(label + '-invalid-' + str(number), command + ['--out', str(out / (label + '-invalid-output-' + str(number))),
                '--check-source-only', *extra], False)
        run(label + '-existing-output', command + ['--out', str(positive), '--check-source-only'], False)
        run(label + '-inside-capsule-output', command + ['--out', str(B / 'forbidden-output'), '--check-source-only'], False)
        run(label + '-missing-environment', command + ['--out', str(out / (label + '-no-environment'))], False)
        helper = ("import importlib.util; p=" + repr(str(B / 'reproduce.py'))
            + "; s=importlib.util.spec_from_file_location('r',p); m=importlib.util.module_from_spec(s); s.loader.exec_module(m); "
            + "m.strict('{\"x\":1,\"x\":2}')")
        run(label + '-duplicate-json', [sys.executable, *flags, '-c', helper], False)
        helper = helper[:helper.index('m.strict')] + "m.strict('{\"x\":NaN}')"
        run(label + '-nonfinite-json', [sys.executable, *flags, '-c', helper], False)
        for token_number, token in enumerate(['sorryAx', 'Lean.ofReduceBool', "declaration uses 'sorry'"]):
            code = helper[:helper.index('m.strict')] + 'm.diagnostic(' + repr(token) + ",'','control')"
            run(label + '-diagnostic-' + str(token_number), [sys.executable, *flags, '-c', code], False)
    # A source-corruption fixture must fail independently of the validator lock.
    fixture = out / 'owned-negative-fixture'
    shutil.copytree(B, fixture)
    lock = json.loads((fixture / 'SOURCE_LOCK.json').read_text())
    changed = fixture / lock['sources'][0]['path']
    changed.write_text(changed.read_text() + '\n-- deliberate control corruption\n')
    for label, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        run(label + '-source-corruption', [sys.executable, *flags, str(fixture / 'reproduce.py'),
            '--out', str(out / (label + '-corruption-result')), '--check-source-only'], False)
    # Check the heavy-family phase policy against every exact locked dependency.
    import importlib.util
    spec = importlib.util.spec_from_file_location('replay', B / 'reproduce.py')
    replay = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replay)
    lock, _ = replay.source_inputs()
    pending = {r['module']: r for r in lock['combined_sources']}
    done = set()
    heavy = {kind: {n for n in pending if replay.group(n) == kind} for kind in replay.GROUPS}
    while pending:
        stage = next((kind for kind in replay.GROUPS if not heavy[kind] <= done), None)
        ready = [n for n, row in pending.items() if set(row['imports']) <= done
                 and replay.group(n) in [None, stage]]
        need(bool(ready), 'heavy-stage policy must drain the exact4057-source DAG')
        for name in ready:
            pending.pop(name)
            done.add(name)
    need(len(done) == 4057, 'complete schedule')
    fixture_lock = sha(fixture / 'SOURCE_LOCK.json')
    need(fixture.parent == out and fixture.name == 'owned-negative-fixture'
         and fixture.is_dir() and not fixture.is_symlink(), 'owned disposable fixture deletion boundary')
    shutil.rmtree(fixture)
    result = dict(status='PASS4057_PREPARED_SOURCE_CLI_CONTROLS_NOT_PROOF_REPLAY',
        routes=len(records), optimization_modes=[0, 1, 2], records=records,
        source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), reproducer_lock_sha256=sha(B / 'REPRODUCER_LOCK.json'),
        scheduler_dag_modules=4057, completed_proof_replay=False,
        removed_regenerable_owned_fixture=dict(path=str(fixture), source_lock_sha256=fixture_lock),
        elapsed_seconds=time.monotonic() - start)
    temp = out / 'RECEIPT.pending'
    temp.write_text(json.dumps(result, indent=2) + '\n')
    os.replace(temp, out / 'RECEIPT.json')
    print(result['status'])

if __name__ == '__main__':
    main()
