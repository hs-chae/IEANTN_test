"""Rebuild all4057 application sources from an empty bank and public libraries.

This is a prepared replay recipe, never an assertion that replay has finished.
The unchanged numerical generators and physical C main run before Lean proofs.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import subprocess
import sys
import time

B = Path(__file__).resolve().parent
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
GROUPS = ['point', 'frame', 'edge', 'cell', 'weight', 'slope']

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def strict(text):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, 'duplicate JSON key: ' + key)
            result[key] = value
        return result
    def invalid(value):
        raise ValueError('nonfinite JSON: ' + value)
    return json.loads(text, object_pairs_hook=pairs, parse_constant=invalid)

def atomic(path, value):
    temp = path.with_suffix('.pending')
    temp.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(temp, path)

def group(name):
    for prefix, kind in [('SourceHeightPointsV2.Point', 'point'),
                         ('SourceMainFramesV1.Point', 'frame'),
                         ('SourceHeightEdgesV1.Edge', 'edge'),
                         ('SourceMainBudgetV1.Cell', 'cell'),
                         ('SourceMainWeightsV1.Block', 'weight'),
                         ('SourcePointSlopesV1.Block', 'slope')]:
        if name.startswith(prefix):
            return kind
    return None

def prior_module():
    spec = importlib.util.spec_from_file_location('locked_complete_main', B / 'base/reproduce.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def source_inputs(check_validator=True):
    lock = strict((B / 'SOURCE_LOCK.json').read_text())
    if check_validator:
        pins = strict((B / 'REPRODUCER_LOCK.json').read_text())
        expected = ['reproduce.py', 'check_controls.py', 'README.md', 'prepare.py',
                    'SOURCE_LOCK.json', 'PROVENANCE.json', 'BOOTSTRAP_FILES.json']
        need([r['path'] for r in pins['files']] == expected, 'exact validator population')
        for row in pins['files']:
            p = B / row['path']
            need(p.is_file() and not p.is_symlink() and p.stat().st_size == row['bytes']
                 and sha(p) == row['sha256'], 'validator pin: ' + row['path'])
    bootstrap = strict((B / 'BOOTSTRAP_FILES.json').read_text())
    for row in bootstrap['files']:
        p = B / row['path']
        need(p.is_file() and not p.is_symlink() and p.stat().st_size == row['bytes']
             and sha(p) == row['sha256'], 'public bootstrap pin: ' + row['path'])
    previous = prior_module()
    full, append, original, runner = previous.source_inputs()
    need(sha(B / 'base/SOURCE_LOCK.json') == lock['prior_source_lock_sha256'], 'prior3942 association')
    names = {r['module'] for r in lock['combined_sources']}
    need(len(names) == len(lock['combined_sources']) == 4057, 'exact4057 source identities')
    need(len(lock['sources']) == 115 and len(lock['combined_roots']) ==
         len(set(lock['combined_roots'])) == 12234, 'exact115 additions/12234 roots')
    need(all(set(r['imports']) <= names for r in lock['combined_sources']), 'complete application import closure')
    for row in lock['combined_sources']:
        p = B / row['path']
        need(p.is_file() and not p.is_symlink() and p.stat().st_size == row['bytes']
             and sha(p) == row['sha256'], 'source identity: ' + row['path'])
        need((B / row['source_root']).resolve() in p.resolve().parents, 'source root association')
    need(not list(B.rglob('*.olean')), 'source capsule must contain no application objects')
    expected_sources = {row['path'] for row in lock['combined_sources']}
    actual_sources = {str(p.relative_to(B)) for root in ['source', 'base/source',
        'base/base/source', 'base/base/base/source'] for p in (B / root).rglob('*.lean')}
    need(actual_sources == expected_sources, 'exact complete source population')
    return lock, runner

def diagnostic(stdout, stderr, name):
    need(not any(token in stdout + stderr for token in ["declaration uses 'sorry'",
         'declaration uses `sorry`', 'sorryAx', 'Lean.ofReduceBool']), 'admitted/native diagnostic: ' + name)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--environment', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=14)
    parser.add_argument('--point-jobs', type=int, default=8)
    parser.add_argument('--frame-jobs', type=int, default=14)
    parser.add_argument('--edge-jobs', type=int, default=14)
    parser.add_argument('--cell-jobs', type=int, default=12)
    parser.add_argument('--weight-jobs', type=int, default=6)
    parser.add_argument('--slope-jobs', type=int, default=6)
    parser.add_argument('--check-source-only', action='store_true')
    args = parser.parse_args()
    need(1 <= args.jobs <= 16 and all(1 <= getattr(args, kind + '_jobs') <= args.jobs
         for kind in GROUPS), 'worker counts1..16 and heavy counts1..jobs')
    lock, prior = source_inputs()
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents, 'fresh output outside immutable capsule')
    if args.check_source_only:
        out.mkdir(parents=True)
        atomic(out / 'RECEIPT.json', dict(status='PASS4057_SOURCE_IDENTITIES_ONLY_NOT_REPLAY',
            source_modules=4057, theorem_roots=12234, application_object_inputs=[],
            source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), proof_replay_completed=False))
        return
    need(args.environment is not None, 'pinned public generic environment required')
    environment = prior.environment_inputs(args.environment.resolve(), lock)
    out.mkdir(parents=True)
    logs, bank = out / 'logs', out / 'objects'
    logs.mkdir()
    bank.mkdir()
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(bank)] + [d['objects'] for d in environment['generic_dependencies']])
    env['LEAN_NUM_THREADS'] = '1'
    records = []
    start = time.monotonic()
    def execute(name, command, lean=False):
        stdout, stderr, timing = [logs / (name + suffix) for suffix in ['.stdout', '.stderr', '.time']]
        began = time.monotonic()
        with stdout.open('w') as f, stderr.open('w') as g:
            q = subprocess.run(['/usr/bin/time', '-v', '-o', str(timing), *command],
                               stdout=f, stderr=g, cwd=B, env=env)
        row = dict(name=name, command=command, exit_code=q.returncode,
            seconds=time.monotonic() - began, stdout_sha256=sha(stdout),
            stderr_sha256=sha(stderr), time_sha256=sha(timing))
        need(q.returncode == 0, 'failed: ' + name)
        if lean:
            diagnostic(stdout.read_text(), stderr.read_text(), name)
        return row
    def compile_source(row):
        obj = bank / Path(row['module'].replace('.', '/')).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        result = execute(row['module'], [environment['compiler'], '-j1', '-R',
            str(B / row['source_root']), str(B / row['path']), '-o', str(obj)], lean=True)
        result.update(source_sha256=row['sha256'], object_sha256=sha(obj))
        return result
    pending = {r['module']: r for r in lock['combined_sources']}
    done, running = set(), {}
    heavy = {kind: {n for n in pending if group(n) == kind} for kind in GROUPS}
    try:
        flags = ['-OO'] if sys.flags.optimize >= 2 else ['-O'] if sys.flags.optimize else []
        compiler = str(Path(environment['compiler']).with_name('clang'))
        numerics = B / 'base/base/base/numerics'
        records.append(execute('numerical-regeneration', [sys.executable, *flags,
            str(numerics / 'reproduce_height_numerics_v1.py'), '--compiler', compiler,
            '--out', str(out / 'numerics')]))
        records.append(execute('numerical-word-association', [sys.executable, *flags,
            str(numerics / 'verify_regenerated_height_words_v1.py'), '--source-root',
            str(B / 'base/base/base/source'), '--raw-root', str(out / 'numerics'),
            '--out', str(out / 'NUMERICAL_WORD_ASSOCIATION.json')]))
        records.append(execute('actual-cpp-regeneration', [sys.executable, *flags,
            str(B / 'base/base/base/reproduce_cpp.py'), '--compiler', compiler,
            '--out', str(out / 'actual-cpp')]))
        generated = out / 'regenerated-source/SynergyHeightC/MainObservedOutput.lean'
        records.append(execute('observed-source-regeneration', [sys.executable, *flags,
            str(B / 'base/regenerate_observation.py'), '--run', str(out / 'actual-cpp'),
            '--out', str(out / 'observation'), '--source-output', str(generated)]))
        need(sha(generated) == sha(B / 'base/source/SynergyHeightC/MainObservedOutput.lean'),
             'fresh physical C output reproduces exact locked observed Lean source')
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            while pending or running:
                stage = next((kind for kind in GROUPS if not heavy[kind] <= done), None)
                ready = [n for n, row in pending.items() if set(row['imports']) <= done]
                for name in ready:
                    if len(running) >= args.jobs:
                        break
                    kind = group(name)
                    if kind is not None and (kind != stage or sum(group(n) == kind for n in running.values())
                                              >= getattr(args, kind + '_jobs')):
                        continue
                    running[executor.submit(compile_source, pending.pop(name))] = name
                need(bool(running), 'cycle/missing dependency or invalid heavy phase schedule')
                complete, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in complete:
                    name = running.pop(future)
                    records.append(future.result())
                    done.add(name)
                    atomic(out / 'CHECKPOINT.json', dict(status='PARTIAL_NOT_ACCEPTED',
                        source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), records=records))
                    atomic(out / 'PROGRESS.json', dict(completed=len(done), total=4057,
                        stage=stage, groups={k: len(v & done) for k, v in heavy.items()},
                        seconds=time.monotonic() - start))
        roots = lock['combined_roots']
        audit = out / 'Audit.lean'
        audit_text = ''.join('import ' + n + '\n' for n in lock['combined_root_modules'])
        audit_text += 'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
        for begin in range(0, len(roots), 64):
            audit_text += 'run_elab do\n let env ← getEnv\n for n in ([' + ','.join('`' + n for n in roots[begin:begin + 64])
            audit_text += '] : List Name) do\n  let some _ := env.find? n | throwError "missing {n}"\n'
            audit_text += '  let ax ← Lean.collectAxioms n\n  logInfo m!"RATIONAL_AUDIT {(Json.mkObj [("name",toJson n.toString),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n'
        audit.write_text(audit_text)
        records.append(execute('audit', [environment['compiler'], '-j1', '-R', str(out), str(audit)], lean=True))
        audits = [strict(s.split('RATIONAL_AUDIT ', 1)[1])
            for s in (logs / 'audit.stdout').read_text().splitlines() if 'RATIONAL_AUDIT ' in s]
        need(len(audits) == 12234 and [r['name'] for r in audits] == roots
             and all(set(r['axioms']) <= STD3 for r in audits), 'exact12234 complete standard-axiom closures')
        expected = {str(Path(r['module'].replace('.', '/')).with_suffix('.olean'))
                    for r in lock['combined_sources']}
        need({str(p.relative_to(bank)) for p in bank.rglob('*.olean')} == expected, 'exact4057 source-built objects')
        source_inputs()
        prior.environment_inputs(args.environment.resolve(), lock)
    except Exception as exc:
        atomic(out / 'FAILURE.json', dict(status='FAILED_PRESERVED_NOT_ACCEPTED', error=str(exc),
            records=records, elapsed_seconds=time.monotonic() - start))
        raise
    result = dict(status='PASS4057_FRESH_SOURCE_MAIN_OBSERVED_RATIONAL_ANT',
        source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), reproducer_sha256=sha(Path(__file__)),
        reproducer_lock_sha256=sha(B / 'REPRODUCER_LOCK.json'), source_modules=4057,
        selected_theorem_roots=12234, final_root=lock['final_source_root'],
        records=records, audits=audits, elapsed_seconds=time.monotonic() - start,
        application_object_inputs=[], completed_fresh_source_graph=True,
        namespace_isolated=False, universal_host_IO_success=False,
        qualification='Selected source-first program and conditional ANT chain plus rational refinement. Model stdio uses explicit all-success semantics; actual fresh output association is checked separately. Pinned generic compiler/kernel/library/runtime/ABI/OS/hardware contracts remain. Namespace isolation is separately attested; original68-body migration is not implied.')
    atomic(out / 'RECEIPT.json', result)
    print(json.dumps({k: result[k] for k in ['status', 'source_modules', 'selected_theorem_roots', 'elapsed_seconds']}))

if __name__ == '__main__':
    main()
