"""Clean complete-main source extension, seeded only from a validated fresh graph.

The mathematical sources and all observed-output statements are locked. The raw
C program is regenerated and the observation Lean source is reproduced before
proof compilation. Successful model policy never means all real host I/O works.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import time

B = Path(__file__).resolve().parent
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
PASS = 'PASS_SOURCE_COLD_COMPLETE_MODELED_MAIN_OBSERVED_OUTPUT_ANT'

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def atomic(path, value):
    temp = path.with_suffix('.pending')
    temp.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(temp, path)

def diagnostic(stdout, stderr, name):
    need(not any(s in stdout + stderr for s in ["declaration uses 'sorry'",
        'declaration uses `sorry`', 'sorryAx', 'Lean.ofReduceBool']), 'admitted/native diagnostic: ' + name)

def prior_module():
    spec = importlib.util.spec_from_file_location('locked_prior_append', B / 'base/reproduce_append.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def source_inputs():
    lock = json.loads((B / 'SOURCE_LOCK.json').read_text())
    pins = json.loads((B / 'REPRODUCER_LOCK.json').read_text())
    expected = ['reproduce.py', 'reproduce_all.py', 'regenerate_observation.py',
                'check_controls.py', 'prepare.py', 'README.md', 'SOURCE_LOCK.json', 'PROVENANCE.json']
    need([r['path'] for r in pins['files']] == expected, 'exact complete-main validator identities')
    for row in pins['files']:
        p = B / row['path']
        need(p.is_file() and not p.is_symlink() and p.stat().st_size == row['bytes']
             and sha(p) == row['sha256'], 'validator identity: ' + row['path'])
    prior = prior_module()
    append, original = prior.source_inputs()
    need(sha(B / 'base/SOURCE_LOCK.json') == lock['base_append_source_lock_sha256']
         and sha(B / 'base/base/SOURCE_LOCK.json') == lock['base_original_source_lock_sha256']
         and sha(B / 'base/REPRODUCER_LOCK.json') == lock['base_validator_lock_sha256'], 'prior lock association')
    old = {r['module'] for frozen in [append, original] for r in frozen['sources']}
    names = {r['module'] for r in lock['sources']}
    need(len(old) == 2272 and len(names) == 1670 and not old & names, 'fixed disjoint source populations')
    need(len(lock['roots']) == len(set(lock['roots'])) == 6363, 'exact distinct new roots')
    need(all(set(r['imports']) <= old | names for r in lock['sources']), 'complete application import closure')
    for row in lock['sources'] + lock['payloads']:
        p = B / row['path']
        need(p.is_file() and not p.is_symlink() and p.stat().st_size == row['bytes']
             and sha(p) == row['sha256'], 'source/payload identity: ' + row['path'])
    return lock, append, original, prior

def validate_prior(run, lock, append, original, prior):
    path = run / 'RECEIPT.json'
    outer = json.loads(path.read_text())
    if outer['status'] == 'PASS_COMPLETE_BASE_PLUS_ACTUAL_FRAME_WEIGHT_ANT_REPRODUCTION':
        need(sha(run / 'append-run/RECEIPT.json') == outer['append_receipt_sha256'], 'prior pipeline/append association')
        run = run / 'append-run'
        path = run / 'RECEIPT.json'
    receipt = json.loads(path.read_text())
    need(receipt['status'] == 'PASS_SOURCE_COLD_APPEND_ACTUAL_FRAMES_WEIGHTS_ANT'
         and receipt['combined_fresh_replay_completed'] is True
         and receipt['append_source_modules'] == 860 and receipt['combined_source_modules'] == 2272
         and receipt['combined_distinct_theorem_roots'] == 5613
         and receipt['outside_application_object_inputs'] == []
         and receipt['source_lock_sha256'] == lock['base_append_source_lock_sha256']
         and receipt['reproducer_sha256'] == sha(B / 'base/reproduce_append.py')
         and receipt['reproducer_lock_sha256'] == lock['base_validator_lock_sha256'], 'complete corrected source-cold prior acceptance')
    association_path = run / 'BASE_ASSOCIATION.json'
    need(sha(association_path) == receipt['base_association_sha256'], 'prior fresh base association')
    old_association = json.loads(association_path.read_text())
    _, validated = prior.validated_base(Path(old_association['base_run']), original, append)
    need(validated == old_association, 'independently validated same-pipeline fresh1412 base')
    seeded_path = run / 'SEEDED_BASE_OBJECTS.json'
    need(sha(seeded_path) == receipt['seeded_base_objects_sha256'], 'prior coherent-bank seeding association')
    records = receipt['records']
    names = {r['module'] for r in append['sources']}
    need(len(records) == 862 and {r['name'] for r in records} == names | {'seed-imports', 'audit'},
         'complete prior actual compile/import/audit population')
    records_by_name = {r['name']: r for r in records}
    for name, row in records_by_name.items():
        need(row['exit_code'] == 0, 'prior compiler exit: ' + name)
        for suffix, field in [('.stdout', 'stdout_sha256'), ('.stderr', 'stderr_sha256'), ('.time', 'time_sha256')]:
            p = run / 'logs' / (name + suffix)
            need(p.is_file() and sha(p) == row[field], 'prior log association: ' + name)
        diagnostic((run / 'logs' / (name + '.stdout')).read_text(),
                   (run / 'logs' / (name + '.stderr')).read_text(), name)
    bank = run / 'objects'
    objects = []
    for row in validated['associated_objects']:
        p = bank / Path(row['module'].replace('.', '/')).with_suffix('.olean')
        need(p.is_file() and not p.is_symlink() and sha(p) == row['object_sha256'], 'fresh1412 seeded object: ' + row['module'])
        objects.append(row)
    for row in append['sources']:
        name = row['module']
        record = records_by_name[name]
        p = bank / Path(name.replace('.', '/')).with_suffix('.olean')
        command = record['command']
        need(len(command) == 7 and command[1:3] == ['-j1', '-R'] and command[5] == '-o'
             and sha(Path(command[0])) == lock['compiler_sha256']
             and sha(Path(command[4])) == row['sha256']
             and Path(command[6]).resolve() == p.resolve()
             and record['source_sha256'] == row['sha256']
             and p.is_file() and not p.is_symlink() and sha(p) == record['object_sha256'],
             'fresh860 source/object/command association: ' + name)
        objects.append(dict(module=name, source_sha256=row['sha256'], object_sha256=sha(p)))
    expected = {str(Path(row['module'].replace('.', '/')).with_suffix('.olean')) for row in objects}
    need({str(p.relative_to(bank)) for p in bank.rglob('*.olean')} == expected, 'exact coherent2272 object population')
    roots = list(dict.fromkeys(original['roots'] + append['roots']))
    need([r['name'] for r in receipt['audits']] == roots
         and all(set(r['axioms']) <= STD3 for r in receipt['audits']), 'prior5613 complete standard closures')
    raw = [json.loads(line.split('APPEND_AUDIT ', 1)[1])
           for line in (run / 'logs/audit.stdout').read_text().splitlines() if 'APPEND_AUDIT ' in line]
    need(raw == receipt['audits'], 'prior raw compiler audit association')
    return bank, dict(status='VALIDATED_COMPLETE_SOURCE_COLD_2272_GRAPH', prior_run=str(run),
        prior_receipt_sha256=sha(path), objects=objects, source_modules=2272, theorem_roots=5613,
        outside_application_object_inputs=[])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--environment', type=Path)
    parser.add_argument('--prior-run', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=14)
    parser.add_argument('--edge-jobs', type=int, default=14)
    parser.add_argument('--cell-jobs', type=int, default=12)
    parser.add_argument('--check-source-only', action='store_true')
    args = parser.parse_args()
    need(1 <= args.jobs <= 16 and 1 <= args.edge_jobs <= args.jobs
         and 1 <= args.cell_jobs <= args.jobs, 'explicit bounded jobs1..16')
    lock, append, original, prior = source_inputs()
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents, 'fresh output outside capsule')
    if args.check_source_only:
        out.mkdir(parents=True)
        atomic(out / 'RECEIPT.json', dict(status='PASS_COMPLETE_MAIN_INPUT_IDENTITIES_ONLY_NOT_REPLAY',
            base_modules=2272, additional_modules=1670, total_modules=3942,
            final_roots=11976, source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), proof_replay_completed=False))
        return
    need(args.environment is not None and args.prior_run is not None, 'environment and completed fresh prior graph required')
    environment = prior.environment_inputs(args.environment.resolve(), lock)
    prior_bank, association = validate_prior(args.prior_run.resolve(), lock, append, original, prior)
    out.mkdir(parents=True)
    atomic(out / 'PRIOR_ASSOCIATION.json', association)
    logs, bank = out / 'logs', out / 'objects'
    logs.mkdir()
    bank.mkdir()
    for row in association['objects']:
        rel = Path(row['module'].replace('.', '/')).with_suffix('.olean')
        target = bank / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(prior_bank / rel, target)
        need(sha(target) == row['object_sha256'], 'coherent fresh object seeding: ' + row['module'])
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
        row = dict(name=name, command=command, exit_code=q.returncode, seconds=time.monotonic() - began,
                   stdout_sha256=sha(stdout), stderr_sha256=sha(stderr), time_sha256=sha(timing))
        need(q.returncode == 0, 'failed: ' + name)
        if lean:
            diagnostic(stdout.read_text(), stderr.read_text(), name)
        return row
    def compile_source(row):
        obj = bank / Path(row['module'].replace('.', '/')).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        result = execute(row['module'], [environment['compiler'], '-j1', '-R', str(B / 'source'),
            str(B / row['path']), '-o', str(obj)], lean=True)
        result.update(source_sha256=row['sha256'], object_sha256=sha(obj))
        return result
    pending = {r['module']: r for r in lock['sources']}
    old_names = {r['module'] for frozen in [original, append] for r in frozen['sources']}
    edges = {n for n in pending if n.startswith('SourceHeightEdgesV1.Edge')}
    done, running = set(), {}
    def is_edge(name):
        return name.startswith('SourceHeightEdgesV1.Edge')
    def is_cell(name):
        return name.startswith('SourceMainBudgetV1.Cell')
    try:
        flags = ['-OO'] if sys.flags.optimize >= 2 else ['-O'] if sys.flags.optimize else []
        records.append(execute('actual-cpp-regeneration', [sys.executable, *flags,
            str(B / 'base/base/reproduce_cpp.py'), '--compiler', str(Path(environment['compiler']).with_name('clang')),
            '--out', str(out / 'actual-cpp')]))
        generated = out / 'regenerated-source/SynergyHeightC/MainObservedOutput.lean'
        records.append(execute('observed-source-regeneration', [sys.executable, *flags,
            str(B / 'regenerate_observation.py'), '--run', str(out / 'actual-cpp'),
            '--out', str(out / 'observation'), '--source-output', str(generated)]))
        need(sha(generated) == sha(B / 'source/SynergyHeightC/MainObservedOutput.lean'),
             'fresh physical C output reproduces exact locked observed Lean source')
        atomic(out / 'OBSERVATION_ASSOCIATION.json', dict(status='PASS_FRESH_C_OUTPUT_AND_LOCKED_LEAN_OBSERVATION_IDENTITY',
            raw_receipt_sha256=sha(out / 'actual-cpp/RECEIPT.json'), raw_output_sha256=sha(out / 'actual-cpp/output.bin'),
            generated_source_sha256=sha(generated), source_lock_sha256=sha(B / 'SOURCE_LOCK.json')))
        probe = out / 'SeedImports.lean'
        probe.write_text('import ScopedC.ArraySourceCallExecute\nimport SourceMainWeightsV1.PNT\n')
        records.append(execute('seed-imports', [environment['compiler'], '-j1', '-R', str(out), str(probe)], lean=True))
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            while pending or running:
                ready = [n for n, row in pending.items() if set(row['imports']) <= done | old_names]
                for name in ready:
                    if len(running) >= args.jobs:
                        break
                    current = list(running.values())
                    if is_edge(name) and sum(is_edge(n) for n in current) >= args.edge_jobs:
                        continue
                    if is_cell(name) and (not edges <= done or sum(is_cell(n) for n in current) >= args.cell_jobs):
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
                    atomic(out / 'PROGRESS.json', dict(completed=len(done), total=1670,
                        edges_completed=len(edges & done), edges_total=768,
                        cells_completed=sum(is_cell(n) for n in done), cells_total=768,
                        seconds=time.monotonic() - start))
        roots = list(dict.fromkeys(original['roots'] + append['roots'] + lock['roots']))
        modules = list(dict.fromkeys(original['root_modules'] + append['root_modules'] + lock['root_modules']))
        audit = out / 'Audit.lean'
        audit.write_text(''.join('import ' + n + '\n' for n in modules)
            + 'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\n'
            + 'run_elab do\n let env ← getEnv\n for n in ([' + ','.join('`' + n for n in roots)
            + '] : List Name) do\n  let some _ := env.find? n | throwError "missing {n}"\n'
            + '  let ax ← Lean.collectAxioms n\n  logInfo m!"COMPLETE_AUDIT '
            + '{(Json.mkObj [("name",toJson n.toString),("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n')
        records.append(execute('audit', [environment['compiler'], '-j1', '-R', str(out), str(audit)], lean=True))
        audits = [json.loads(s.split('COMPLETE_AUDIT ', 1)[1])
                  for s in (logs / 'audit.stdout').read_text().splitlines() if 'COMPLETE_AUDIT ' in s]
        need(len(audits) == 11976 and [r['name'] for r in audits] == roots
             and all(set(r['axioms']) <= STD3 for r in audits), 'exact11976 complete final standard-axiom closures')
        source_inputs()
        prior.environment_inputs(args.environment.resolve(), lock)
        validate_prior(args.prior_run.resolve(), lock, append, original, prior)
    except Exception as exc:
        atomic(out / 'FAILURE.json', dict(status='FAILED_PRESERVED_NOT_ACCEPTED', error=str(exc),
            records=records, elapsed_seconds=time.monotonic() - start))
        raise
    result = dict(status=PASS, source_lock_sha256=sha(B / 'SOURCE_LOCK.json'),
        reproducer_sha256=sha(Path(__file__)), reproducer_lock_sha256=sha(B / 'REPRODUCER_LOCK.json'),
        source_modules=3942, additional_source_modules=1670, selected_theorem_roots=11976,
        final_root=lock['final_root'], records=records, audits=audits, elapsed_seconds=time.monotonic() - start,
        prior_association_sha256=sha(out / 'PRIOR_ASSOCIATION.json'),
        observation_association_sha256=sha(out / 'OBSERVATION_ASSOCIATION.json'),
        same_pipeline_fresh_source_built_object_inputs=2272, outside_application_object_inputs=[],
        completed_fresh_source_graph=True, namespace_isolated=False, universal_host_IO_success=False,
        qualification='Complete selected3942-source graph including actual initialized main, all768 source inputs/point/budget/rows, modeled normal stdio, fresh physical final128bytes and unchanged conditional ANT consumer. Public generic compiler/library/runtime/ABI/OS/hardware contracts remain; final namespace-isolated acceptance is separate.')
    atomic(out / 'RECEIPT.json', result)
    print(json.dumps({k: result[k] for k in ['status', 'source_modules', 'selected_theorem_roots', 'elapsed_seconds']}))

if __name__ == '__main__':
    main()
