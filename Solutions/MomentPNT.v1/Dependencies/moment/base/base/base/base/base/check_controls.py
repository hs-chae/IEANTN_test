"""Exercise the actual portable CLIs in all Python optimization modes.

These are reproducer controls, not source/math proof acceptance. The complete
Lean run has its own receipt and does not follow from these checks.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys

B = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--environment', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    need(args.environment.is_file(), 'public environment required')
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents, 'fresh external controls directory')
    out.mkdir(parents=True)
    environment = json.loads(args.environment.read_text())
    compiler = str(Path(environment['compiler']).with_name('clang'))
    lock = json.loads((B / 'SOURCE_LOCK.json').read_text())
    rows = []

    def run(mode, label, command, accepted):
        target = out / (mode + '-' + label)
        with target.with_suffix('.stdout').open('wb') as so, target.with_suffix('.stderr').open('wb') as se:
            child = subprocess.run(command, stdout=so, stderr=se, timeout=900)
        need((child.returncode == 0) == accepted, mode + ' unexpected CLI result: ' + label)
        rows.append(dict(mode=mode, role=label, command=command,
                         exit_code=child.returncode, expected_acceptance=accepted,
                         stdout_sha256=sha(target.with_suffix('.stdout')),
                         stderr_sha256=sha(target.with_suffix('.stderr'))))

    for flags in [[], ['-O'], ['-OO']]:
        mode = 'normal' if not flags else flags[0][1:]
        python = [sys.executable, *flags]
        raw = out / (mode + '-raw')
        numerics = out / (mode + '-numerics')
        run(mode, 'source-identities', [*python, str(B / 'reproduce.py'), '--check-source-only',
            '--out', str(out / (mode + '-source-only'))], True)
        run(mode, 'actual-cpp', [*python, str(B / 'reproduce_cpp.py'), '--compiler', compiler,
            '--out', str(raw)], True)
        run(mode, 'all-five-numerics', [*python, str(B / 'numerics/reproduce_height_numerics_v1.py'),
            '--compiler', compiler, '--out', str(numerics)], True)
        run(mode, 'numerical-word-association', [*python,
            str(B / 'numerics/verify_regenerated_height_words_v1.py'),
            '--source-root', str(B / 'source'), '--raw-root', str(numerics),
            '--out', str(out / (mode + '-word-association.json'))], True)
        run(mode, 'invalid-point-job-count', [*python, str(B / 'reproduce_all.py'),
            '--environment', str(args.environment.resolve()), '--out', str(out / (mode + '-invalid-jobs')),
            '--jobs', '2', '--point-jobs', '3'], False)
        for child in ['reproduce.py', 'reproduce_all.py', 'prepare_environment.py', 'reproduce_cpp.py',
                      'numerics/reproduce_height_numerics_v1.py',
                      'numerics/verify_regenerated_height_words_v1.py']:
            run(mode, child.replace('/', '_') + '-unknown-option',
                [*python, str(B / child), '--definitely-unknown-option'], False)
        # Corrupt only an isolated source-capsule copy, keeping original sources
        # and the full application proof run untouched.
        fixture = out / (mode + '-corrupt-fixture')
        shutil.copytree(B, fixture, ignore=shutil.ignore_patterns('__pycache__'))
        chosen = fixture / lock['sources'][0]['path']
        chosen.write_bytes(chosen.read_bytes() + b'\n-- deliberately corrupted owned fixture\n')
        run(mode, 'source-corruption-rejected', [*python, str(fixture / 'reproduce.py'),
            '--check-source-only', '--out', str(out / (mode + '-corruption-output'))], False)
        # Child entry points reject original-output reuse before any new work.
        run(mode, 'existing-raw-output-rejected', [*python, str(B / 'reproduce_cpp.py'),
            '--compiler', compiler, '--out', str(raw)], False)
        run(mode, 'existing-numerics-output-rejected', [*python,
            str(B / 'numerics/reproduce_height_numerics_v1.py'), '--compiler', compiler,
            '--out', str(numerics)], False)
        for diagnostic in ["declaration uses 'sorry'", 'declaration uses `sorry`',
                           'sorryAx', 'Lean.ofReduceBool']:
            snippet = '''import importlib.util
s=importlib.util.spec_from_file_location('target',%r)
m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
m.no_admitted_proof(%r,'','negative-control')
''' % (str(B / 'reproduce.py'), diagnostic)
            run(mode, 'proof-diagnostic-' + str(len(rows)), [*python, '-c', snippet], False)
        # All fixture files are copied, regenerable, and exactly inventoried
        # before removal. No source-capsule original or accepted proof is removed.
        fixture_files = [p for p in fixture.rglob('*') if p.is_file()]
        need(fixture.parent == out and fixture.name == mode + '-corrupt-fixture' and
             not fixture.is_symlink(), 'owned cleanup target')
        cleanup = dict(path=str(fixture), files=len(fixture_files),
                       bytes=sum(p.stat().st_size for p in fixture_files),
                       original_source_lock_sha256=sha(B / 'SOURCE_LOCK.json'))
        (out / (mode + '-cleanup-preview.json')).write_text(json.dumps(cleanup, indent=2)+'\n')
        shutil.rmtree(fixture)
        cleanup['removed'] = not fixture.exists()
        need(cleanup['removed'], 'fixture cleanup')
        (out / (mode + '-cleanup-receipt.json')).write_text(json.dumps(cleanup, indent=2)+'\n')
    receipt = dict(status='PASS_ACTUAL_COMPOSITION_REPRODUCER_CLI_CONTROLS_ALL3_MODES',
                   routes=rows, source_lock_sha256=sha(B / 'SOURCE_LOCK.json'),
                   validator_sha256=sha(Path(__file__)),
                   combined_fresh_proof_replay=False,
                   qualification='Actual raw C/regeneration/source-identity/negative CLI controls; '
                   'the complete Lean graph is independently executed and accepted by its own receipt.')
    pending = out / 'RECEIPT.pending'
    pending.write_text(json.dumps(receipt, indent=2)+'\n')
    pending.replace(out / 'RECEIPT.json')
    print(json.dumps({'status': receipt['status'], 'routes': len(rows)}))


if __name__ == '__main__':
    main()
