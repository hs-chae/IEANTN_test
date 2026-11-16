"""Actual complete-main reproduction CLI controls in normal/O/OO modes."""
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
    need(args.environment.is_file() and not out.exists() and B not in out.parents, 'public environment and fresh controls workspace')
    environment = json.loads(args.environment.read_text())
    compiler = Path(environment['compiler']).with_name('clang')
    out.mkdir(parents=True)
    records = []
    def run(name, command, success, receipt=None, status=None):
        start = time.monotonic()
        q = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        stdout, stderr = out / (name + '.stdout'), out / (name + '.stderr')
        stdout.write_bytes(q.stdout)
        stderr.write_bytes(q.stderr)
        need((q.returncode == 0) is success, 'unexpected actual CLI result: ' + name)
        if receipt is not None:
            need(receipt.is_file() and json.loads(receipt.read_text())['status'] == status, 'exact receipt: ' + name)
        records.append(dict(name=name, command=command, exit_code=q.returncode,
            seconds=time.monotonic() - start, stdout_sha256=sha(stdout), stderr_sha256=sha(stderr),
            expected_success=success))
    for mode, flags in [('normal', []), ('O', ['-O']), ('OO', ['-OO'])]:
        prefix = [sys.executable, *flags]
        target = out / (mode + '-source-only')
        run(mode + '-source-only', prefix + [str(B / 'reproduce.py'), '--check-source-only', '--out', str(target)],
            True, target / 'RECEIPT.json', 'PASS_COMPLETE_MAIN_INPUT_IDENTITIES_ONLY_NOT_REPLAY')
        invalids = [['--jobs', '0'], ['--jobs', '17'], ['--edge-jobs', '0'],
                    ['--cell-jobs', '17'], ['--unknown-option']]
        for index, extra in enumerate(invalids):
            run(mode + '-invalid-source-' + str(index), prefix + [str(B / 'reproduce.py'),
                '--check-source-only', '--out', str(out / (mode + '-invalid-' + str(index))), *extra], False)
        run(mode + '-existing-output', prefix + [str(B / 'reproduce.py'), '--check-source-only', '--out', str(target)], False)
        for index, extra in enumerate([['--base-jobs', '0'], ['--prior-jobs', '17'],
            ['--frame-jobs', '17'], ['--weight-jobs', '0'], ['--jobs', '17'],
            ['--edge-jobs', '0'], ['--cell-jobs', '17'], ['--unknown-option']]):
            run(mode + '-invalid-pipeline-' + str(index), prefix + [str(B / 'reproduce_all.py'),
                '--environment', str(args.environment.resolve()),
                '--out', str(out / (mode + '-invalid-pipeline-' + str(index))), *extra], False)
        run(mode + '-missing-prior', prefix + [str(B / 'reproduce.py'),
            '--environment', str(args.environment.resolve()), '--prior-run', str(out / 'missing-prior'),
            '--out', str(out / (mode + '-missing-prior-output'))], False)
        for index, marker in enumerate(["declaration uses 'sorry'", 'declaration uses `sorry`', 'sorryAx', 'Lean.ofReduceBool']):
            code = ('import sys;sys.path.insert(0,' + repr(str(B))
                + ');from reproduce import diagnostic;diagnostic(' + repr(marker) + ',"","negative")')
            run(mode + '-admitted-' + str(index), prefix + ['-c', code], False)
        workspace = out / (mode + '-observation-workspace')
        workspace.mkdir()
        raw = workspace / 'actual-cpp'
        run(mode + '-actual-cpp', prefix + [str(B / 'base/base/reproduce_cpp.py'),
            '--compiler', str(compiler), '--out', str(raw)], True, raw / 'RECEIPT.json',
            'RAW_ACTUAL_CPP_OUTPUT_ASSOCIATION_PASS')
        observation = workspace / 'observation'
        generated = workspace / 'generated/SynergyHeightC/MainObservedOutput.lean'
        command = prefix + [str(B / 'regenerate_observation.py'), '--run', str(raw),
            '--out', str(observation), '--source-output', str(generated)]
        run(mode + '-observation', command, True, observation / 'PREPARATION.json',
            'OBSERVATION_PREPARED_REQUIRES_LEAN_SOURCE_COMPARISON')
        need(sha(generated) == sha(B / 'source/SynergyHeightC/MainObservedOutput.lean'), 'actual raw observation regenerates locked source')
        run(mode + '-existing-observation', command, False)
        run(mode + '-unknown-observation', command + ['--unknown-option'], False)
        malformed = workspace / 'malformed-cpp'
        shutil.copytree(raw, malformed)
        p = malformed / 'output.bin'
        data = p.read_bytes()
        p.write_bytes(bytes([data[0] ^ 1]) + data[1:])
        run(mode + '-corrupt-observation', prefix + [str(B / 'regenerate_observation.py'),
            '--run', str(malformed), '--out', str(workspace / 'bad-observation'),
            '--source-output', str(workspace / 'bad-generated/SynergyHeightC/MainObservedOutput.lean')], False)
        fixture = out / (mode + '-corrupt-source-capsule')
        shutil.copytree(B, fixture, ignore=shutil.ignore_patterns('__pycache__'))
        lock = json.loads((fixture / 'SOURCE_LOCK.json').read_text())
        p = fixture / lock['sources'][-1]['path']
        original = sha(p)
        p.write_bytes(p.read_bytes() + b'\n-- deliberate pinned-source negative fixture\n')
        run(mode + '-corrupt-source', prefix + [str(fixture / 'reproduce.py'),
            '--check-source-only', '--out', str(out / (mode + '-bad-source-output'))], False)
        files = [p for p in fixture.rglob('*') if p.is_file()]
        cleanup = dict(status='VERIFIED_OWNED_REGENERABLE_SOURCE_NEGATIVE_CLEANUP', directory=str(fixture),
            files=len(files), regular_file_bytes=sum(p.stat().st_size for p in files),
            original_target_sha256=original, reason='Disposable checked source-corruption copy; original sources and control evidence retained.')
        need(fixture.parent == out and not fixture.is_symlink(), 'verified owned negative cleanup target')
        (out / (mode + '-cleanup-preview.json')).write_text(json.dumps(cleanup, indent=2) + '\n')
        shutil.rmtree(fixture)
        need(not fixture.exists(), 'negative source fixture removed')
    result = dict(status='PASS_ACTUAL_COMPLETE_MAIN_CLI_AND_C_OBSERVATION_CONTROLS_NORMAL_O_OO',
        routes=len(records), records=records, source_lock_sha256=sha(B / 'SOURCE_LOCK.json'),
        mathematical_replay_completed=False,
        qualification='Actual source/input CLIs and fresh C/observation regeneration in all three modes. Complete3942-source Lean replay is separate.')
    pending = out / 'RECEIPT.pending'
    pending.write_text(json.dumps(result, indent=2) + '\n')
    pending.replace(out / 'RECEIPT.json')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}))

if __name__ == '__main__':
    main()
