"""Actual CLI acceptance controls in normal, -O and -OO Python modes.

This checks the reproducibility program, not the mathematical theorem. A source
preflight/control success must never be reported as a completed Lean replay.
"""
from pathlib import Path
import argparse
import hashlib
import json
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
    parser.add_argument('--environment', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents and args.environment.is_file(), 'fresh controls/output and public environment')
    out.mkdir(parents=True)
    rows = []
    def run(name, command, success, receipt=None, status=None):
        began = time.monotonic()
        q = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stderr = out / (name + '.stdout'), out / (name + '.stderr')
        stdout.write_bytes(q.stdout)
        stderr.write_bytes(q.stderr)
        need((q.returncode == 0) is success, 'unexpected CLI result: ' + name)
        if receipt is not None:
            need(receipt.is_file() and json.loads(receipt.read_text())['status'] == status,
                 'exact control receipt: ' + name)
        rows.append(dict(name=name, command=command, exit_code=q.returncode, seconds=time.monotonic() - began,
                         stdout_sha256=sha(stdout), stderr_sha256=sha(stderr), expected_success=success))
    for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        prefix = [sys.executable, *flags]
        fresh = out / (mode + '-source-only')
        run(mode + '-source-only', prefix + [str(B / 'reproduce_append.py'), '--check-source-only', '--out', str(fresh)],
            True, fresh / 'RECEIPT.json', 'PASS_APPEND_INPUT_IDENTITIES_ONLY_NOT_LEAN_REPLAY')
        for index, invalid in enumerate([['--jobs', '0'], ['--jobs', '17'], ['--frame-jobs', '0'],
                                         ['--weight-jobs', '17'], ['--unknown-argument']]):
            run(mode + '-append-invalid-' + str(index), prefix + [str(B / 'reproduce_append.py'),
                '--check-source-only', '--out', str(out / (mode + '-bad-append-' + str(index))), *invalid], False)
        run(mode + '-existing-output', prefix + [str(B / 'reproduce_append.py'),
            '--check-source-only', '--out', str(fresh)], False)
        for index, invalid in enumerate([['--base-jobs', '0'], ['--jobs', '17'], ['--frame-jobs', '0'],
                                         ['--weight-jobs', '17'], ['--unknown-argument']]):
            run(mode + '-pipeline-invalid-' + str(index), prefix + [str(B / 'reproduce_all.py'),
                '--environment', str(args.environment.resolve()),
                '--out', str(out / (mode + '-bad-pipeline-' + str(index))), *invalid], False)
        run(mode + '-missing-base', prefix + [str(B / 'reproduce_append.py'),
            '--environment', str(args.environment.resolve()), '--base-run', str(out / 'missing-base'),
            '--out', str(out / (mode + '-missing-base-output'))], False)
        for index, fragment in enumerate(["declaration uses 'sorry'", 'declaration uses `sorry`',
                                           'sorryAx', 'Lean.ofReduceBool']):
            code = ('import sys;sys.path.insert(0,' + repr(str(B)) + ');'
                    'from reproduce_append import diagnostic;diagnostic(' + repr(fragment) + ',"","negative")')
            run(mode + '-admitted-diagnostic-' + str(index), prefix + ['-c', code], False)
        owned = out / (mode + '-corrupted-capsule')
        shutil.copytree(B, owned, ignore=shutil.ignore_patterns('__pycache__'))
        lock = json.loads((owned / 'SOURCE_LOCK.json').read_text())
        target = owned / lock['sources'][-1]['path']
        before = sha(target)
        target.write_bytes(target.read_bytes() + b'\n-- deliberate pinned-source negative fixture\n')
        altered = sha(target)
        need(before != altered, 'actual source corruption fixture')
        run(mode + '-source-corruption', prefix + [str(owned / 'reproduce_append.py'),
            '--check-source-only', '--out', str(out / (mode + '-corruption-output'))], False)
        files = [p for p in owned.rglob('*') if p.is_file()]
        cleanup = dict(status='PREVIEWED_OWNED_REGENERABLE_FIXTURE_CLEANUP', directory=str(owned),
                       files=len(files), regular_file_bytes=sum(p.stat().st_size for p in files),
                       altered_source_sha256=altered, pinned_source_sha256=before,
                       reason='Disposable copied source-corruption fixture; original locked sources and all test receipts retained.')
        need(owned.parent == out and not owned.is_symlink() and owned.name == mode + '-corrupted-capsule',
             'verified controls-owned cleanup target')
        (out / (mode + '-cleanup-preview.json')).write_text(json.dumps(cleanup, indent=2) + '\n')
        shutil.rmtree(owned)
        need(not owned.exists(), 'owned fixture cleanup completed')
    result = dict(status='PASS_ACTUAL_APPEND_CLI_CONTROLS_NORMAL_O_OO', routes=len(rows), records=rows,
                  source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), mathematical_replay_completed=False,
                  qualification='Actual CLI controls and pinned-source rejection only. Positive completed-base acceptance and all Lean proofs require the full replay.')
    pending = out / 'RECEIPT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    pending.replace(out / 'RECEIPT.json')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}))

if __name__ == '__main__':
    main()
