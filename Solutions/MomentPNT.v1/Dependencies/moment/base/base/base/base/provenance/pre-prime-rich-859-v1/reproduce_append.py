"""Rebuild the locked actual-frame/weight/PNT source append.

Only a completely validated fresh base1412 replay supplies application objects.
The original base receipt is never changed. Run within an explicit host resource
scope; this script does not silently impose a historical 4 GiB limit.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import time

B = Path(__file__).resolve().parent
STD3 = {'propext', 'Classical.choice', 'Quot.sound'}
PASS_BASE = 'PASS_SOURCE_COLD_BARE768_C_POINT_TO_ANT_COMPOSITION'
PASS_APPEND = 'PASS_SOURCE_COLD_APPEND_ACTUAL_FRAMES_WEIGHTS_ANT'
BASE_VALIDATORS = ['reproduce.py', 'reproduce_all.py', 'reproduce_cpp.py',
    'prepare_environment.py', 'numerics/reproduce_height_numerics_v1.py',
    'numerics/verify_regenerated_height_words_v1.py', 'SOURCE_LOCK.json',
    'CPP_ASSOCIATION_PIN.json', 'numerics/HEIGHT_REGEN_MANIFEST_V1.json']
OWN_VALIDATORS = ['reproduce_append.py', 'reproduce_all.py', 'check_controls.py',
    'prepare.py', 'README.md', 'PROVENANCE.json', 'SOURCE_LOCK.json', 'base/CAPSULE_MANIFEST.json']

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def atomic(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix('.pending')
    temp.write_text(json.dumps(value, indent=2) + '\n')
    os.replace(temp, path)

def diagnostic(stdout, stderr, name):
    text = stdout + stderr
    need(not any(x in text for x in ["declaration uses 'sorry'", 'declaration uses `sorry`',
         'sorryAx', 'Lean.ofReduceBool']), 'admitted/native proof diagnostic: ' + name)

def source_inputs():
    validators = json.loads((B / 'REPRODUCER_LOCK.json').read_text())
    expected = OWN_VALIDATORS + ['base/' + p for p in BASE_VALIDATORS]
    need([r['path'] for r in validators['files']] == expected, 'exact reproducer identity population')
    for row in validators['files']:
        p = B / row['path']
        need(p.is_file() and not p.is_symlink() and p.stat().st_size == row['bytes']
             and sha(p) == row['sha256'], 'reproducer/source-lock identity: ' + row['path'])
    lock_path = B / 'SOURCE_LOCK.json'
    lock = json.loads(lock_path.read_text())
    base_path = B / 'base/SOURCE_LOCK.json'
    base = json.loads(base_path.read_text())
    need(sha(base_path) == lock['base_source_lock_sha256'], 'immutable base lock')
    need(len(base['sources']) == 1412 and len(base['roots']) == 2350, 'base population')
    need(len(lock['sources']) == 859 and len(lock['roots']) == 3262, 'append population')
    names = {r['module'] for r in lock['sources']}
    old_names = {r['module'] for r in base['sources']}
    need(len(names) == 859 and not names & old_names, 'distinct additive compiler identities')
    need(len(set(lock['roots'])) == 3262, 'distinct append root identities')
    need(all(set(r['imports']) <= names | old_names for r in lock['sources']), 'complete source closure')
    for directory, frozen in [(B, lock), (B / 'base', base)]:
        for row in frozen['sources'] + frozen['payloads']:
            p = directory / row['path']
            need(p.is_file() and not p.is_symlink() and p.stat().st_size == row['bytes']
                 and sha(p) == row['sha256'], 'source/payload identity: ' + str(p))
    return lock, base

def environment_inputs(path, lock):
    need(path.is_file(), 'pinned public generic environment file required')
    e = json.loads(path.read_text())
    compiler = Path(e['compiler'])
    tool = compiler.parent.parent
    need(sha(compiler) == lock['compiler_sha256'], 'compiler identity')
    for row in lock['runtime_pins']['toolchain_files']:
        p = tool / row['path']
        need(p.is_file() and p.stat().st_size == row['bytes'] and sha(p) == row['sha256'],
             'compiler/kernel runtime identity: ' + row['path'])
    q = subprocess.run([str(compiler), '--version'], capture_output=True, text=True, check=True)
    need(q.stdout.strip() == lock['runtime_pins']['lean_version'], 'Lean version identity')
    deps = e['generic_dependencies']
    need([{k: d[k] for k in ['name', 'commit', 'url']} for d in deps] == lock['generic_dependencies'],
         'exact public generic dependency population')
    for d in deps:
        q = subprocess.run(['git', '-C', d['source'], 'rev-parse', 'HEAD'],
                           capture_output=True, text=True, check=True)
        need(q.stdout.strip() == d['commit'] and Path(d['objects']).is_dir(),
             'pinned public source/cache: ' + d['name'])
    return e

def validated_base(run, base, lock):
    need(run.is_dir(), 'completed fresh base run directory required')
    outer_path = run / 'RECEIPT.json'
    outer = json.loads(outer_path.read_text())
    need(outer['status'] == 'PASS_FRESH_BARE768_SOURCE_POINT_ANT_WITH_REGENERATION'
         and outer['combined_fresh_replay_completed'] is True, 'complete base pipeline acceptance')
    p = run / 'proofs'
    receipt_path = p / 'RECEIPT.json'
    need(sha(receipt_path) == outer['proof_receipt_sha256'], 'base outer/proof association')
    receipt = json.loads(receipt_path.read_text())
    need(receipt['status'] == PASS_BASE and receipt['source_modules'] == 1412
         and receipt['payloads'] == 574 and receipt['theorem_roots'] == 2350
         and receipt['application_object_inputs'] == []
         and receipt['combined_fresh_replay_completed'] is True
         and receipt['source_lock_sha256'] == lock['base_source_lock_sha256'],
         'complete source-cold base acceptance')
    need(outer['source_lock_sha256'] == lock['base_source_lock_sha256'], 'base pipeline lock association')
    pins_path = run / 'VALIDATOR_PINS_V1.json'
    pins = json.loads(pins_path.read_text())
    need([x['path'] for x in pins['files']] == BASE_VALIDATORS, 'exact base validator/lock identities')
    for row in pins['files']:
        script = B / 'base' / row['path']
        need(script.is_file() and script.stat().st_size == row['bytes']
             and sha(script) == row['sha256'], 'base validator identity: ' + row['path'])
    need(receipt['reproducer_sha256'] == sha(B / 'base/reproduce.py'), 'actual base proof reproducer pin')
    names = {r['module'] for r in base['sources']}
    records = receipt['records']
    need(len(records) == 1413 and {r['name'] for r in records} == names | {'audit'},
         'complete distinct base compile/audit population')
    by_name = {r['name']: r for r in records}
    for name, row in by_name.items():
        need(row['exit_code'] == 0, 'base compiler exit: ' + name)
        files = {suffix: p / 'logs' / (name + suffix) for suffix in ['.stdout', '.stderr', '.time']}
        for suffix, key in [('.stdout', 'stdout_sha256'), ('.stderr', 'stderr_sha256'), ('.time', 'time_sha256')]:
            need(files[suffix].is_file() and sha(files[suffix]) == row[key], 'base log association: ' + name)
        diagnostic(files['.stdout'].read_text(), files['.stderr'].read_text(), name)
    associated = []
    for source in base['sources']:
        name = source['module']
        row = by_name[name]
        obj = p / 'objects' / Path(name.replace('.', '/')).with_suffix('.olean')
        need(obj.is_file() and not obj.is_symlink() and sha(obj) == row['object_sha256'],
             'fresh source-built base object: ' + name)
        command = row['command']
        need(len(command) == 7 and command[1:3] == ['-j1', '-R'] and command[5] == '-o',
             'base exact compile command: ' + name)
        actual_source = Path(command[4])
        need(sha(Path(command[0])) == lock['compiler_sha256']
             and actual_source.is_file() and sha(actual_source) == source['sha256']
             and Path(command[6]).resolve() == obj.resolve(), 'base source/object association: ' + name)
        associated.append(dict(module=name, source_sha256=source['sha256'], object_sha256=sha(obj)))
    audits = receipt['audits']
    need([x['name'] for x in audits] == base['roots']
         and all(set(x['axioms']) <= STD3 for x in audits), 'base complete standard-axiom closures')
    raw = [json.loads(line.split('BODY_AUDIT ', 1)[1])
           for line in (p / 'logs/audit.stdout').read_text().splitlines() if 'BODY_AUDIT ' in line]
    need(raw == audits, 'base raw/compiler axiom audit association')
    return p / 'objects', dict(status='VALIDATED_COMPLETE_SOURCE_COLD_BASE',
        base_run=str(run), pipeline_receipt_sha256=sha(outer_path), proof_receipt_sha256=sha(receipt_path),
        validator_pins_sha256=sha(pins_path),
        source_lock_sha256=lock['base_source_lock_sha256'], source_modules=1412,
        theorem_roots=2350, associated_objects=associated, outside_application_object_inputs=[])

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--environment', type=Path)
    parser.add_argument('--base-run', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=14)
    parser.add_argument('--frame-jobs', type=int, default=14)
    parser.add_argument('--weight-jobs', type=int, default=6)
    parser.add_argument('--check-source-only', action='store_true')
    args = parser.parse_args()
    need(1 <= args.jobs <= 16 and 1 <= args.frame_jobs <= args.jobs
         and 1 <= args.weight_jobs <= args.jobs, 'explicit jobs1..16 and bounded heavy phases')
    lock, base = source_inputs()
    out = args.out.resolve()
    need(not out.exists() and B not in out.parents, 'fresh output outside source capsule')
    if args.check_source_only:
        out.mkdir(parents=True)
        atomic(out / 'RECEIPT.json', dict(status='PASS_APPEND_INPUT_IDENTITIES_ONLY_NOT_LEAN_REPLAY',
            base_source_modules=1412, append_source_modules=859, append_theorem_roots=3262,
            source_lock_sha256=sha(B / 'SOURCE_LOCK.json'), combined_fresh_replay_completed=False))
        return
    need(args.environment is not None and args.base_run is not None, 'environment and completed base run required')
    e = environment_inputs(args.environment.resolve(), lock)
    base_objects, association = validated_base(args.base_run.resolve(), base, lock)
    out.mkdir(parents=True)
    atomic(out / 'BASE_ASSOCIATION.json', association)
    objects, logs = out / 'objects', out / 'logs'
    objects.mkdir()
    logs.mkdir()
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(objects), str(base_objects)]
                               + [d['objects'] for d in e['generic_dependencies']])
    env['LEAN_NUM_THREADS'] = '1'
    start = time.monotonic()
    records = []
    def execute(name, command):
        stdout, stderr, timing = [logs / (name + suffix) for suffix in ['.stdout', '.stderr', '.time']]
        began = time.monotonic()
        with stdout.open('w') as f, stderr.open('w') as g:
            q = subprocess.run(['/usr/bin/time', '-v', '-o', str(timing), *command],
                               stdout=f, stderr=g, cwd=B, env=env)
        row = dict(name=name, command=command, exit_code=q.returncode,
                   seconds=time.monotonic() - began, stdout_sha256=sha(stdout),
                   stderr_sha256=sha(stderr), time_sha256=sha(timing))
        need(q.returncode == 0, 'compiler failed: ' + name)
        diagnostic(stdout.read_text(), stderr.read_text(), name)
        return row
    def compile_source(row):
        obj = objects / Path(row['module'].replace('.', '/')).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        result = execute(row['module'], [e['compiler'], '-j1', '-R', str(B / 'source'),
                         str(B / row['path']), '-o', str(obj)])
        result.update(source_sha256=row['sha256'], object_sha256=sha(obj))
        return result
    pending = {r['module']: r for r in lock['sources']}
    old_names = {r['module'] for r in base['sources']}
    done, running = set(), {}
    frames = {n for n in pending if n.startswith('SourceMainFramesV1.Point')}
    def frame(name):
        return name.startswith('SourceMainFramesV1.Point')
    def weight(name):
        return name.startswith('SourceMainWeightsV1.Block')
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            while pending or running:
                ready = [n for n, row in pending.items() if set(row['imports']) <= done | old_names]
                for name in ready:
                    if len(running) >= args.jobs:
                        break
                    live = list(running.values())
                    if frame(name) and sum(frame(n) for n in live) >= args.frame_jobs:
                        continue
                    if weight(name) and (not frames <= done
                                         or sum(weight(n) for n in live) >= args.weight_jobs):
                        continue
                    running[executor.submit(compile_source, pending.pop(name))] = name
                need(bool(running), 'cycle/missing dependency or invalid phase scheduling')
                completed, _ = concurrent.futures.wait(running,
                    return_when=concurrent.futures.FIRST_COMPLETED)
                for future in completed:
                    name = running.pop(future)
                    records.append(future.result())
                    done.add(name)
                    atomic(out / 'CHECKPOINT.json', dict(status='PARTIAL_NOT_ACCEPTED',
                        source_lock_sha256=sha(B / 'SOURCE_LOCK.json'),
                        base_association_sha256=sha(out / 'BASE_ASSOCIATION.json'), records=records))
                    atomic(out / 'PROGRESS.json', dict(completed=len(done), total=859,
                        framed_completed=len(frames & done), framed_total=768,
                        weight_completed=sum(weight(n) for n in done), weight_total=24,
                        seconds=time.monotonic() - start))
        root_names = list(dict.fromkeys(base['roots'] + lock['roots']))
        module_names = list(dict.fromkeys(base['root_modules'] + lock['root_modules']))
        audit = out / 'Audit.lean'
        audit.write_text(''.join('import ' + n + '\n' for n in module_names)
            + 'import Lean.Util.CollectAxioms\nopen Lean Elab\nset_option maxHeartbeats 0\n'
            + 'run_elab do\n let env ← getEnv\n for n in (['
            + ','.join('`' + n for n in root_names) + '] : List Name) do\n'
            + '  let some _ := env.find? n | throwError "missing {n}"\n'
            + '  let ax ← Lean.collectAxioms n\n'
            + '  logInfo m!"APPEND_AUDIT {(Json.mkObj [("name",toJson n.toString),'
            + '("axioms",toJson (ax.toList.map Name.toString))]).compress}"\n')
        records.append(execute('audit', [e['compiler'], '-j1', '-R', str(out), str(audit)]))
        audits = [json.loads(line.split('APPEND_AUDIT ', 1)[1])
                  for line in (logs / 'audit.stdout').read_text().splitlines() if 'APPEND_AUDIT ' in line]
        need([r['name'] for r in audits] == root_names
             and all(set(r['axioms']) <= STD3 for r in audits), 'complete final standard-axiom closures')
        source_inputs()
        environment_inputs(args.environment.resolve(), lock)
        validated_base(args.base_run.resolve(), base, lock)
    except Exception as exc:
        atomic(out / 'FAILURE.json', dict(status='FAILED_PRESERVED_NOT_ACCEPTED', error=str(exc),
            records=records, seconds=time.monotonic() - start))
        raise
    result = dict(status=PASS_APPEND, source_lock_sha256=sha(B / 'SOURCE_LOCK.json'),
        reproducer_sha256=sha(Path(__file__)), base_association_sha256=sha(out / 'BASE_ASSOCIATION.json'),
        reproducer_lock_sha256=sha(B / 'REPRODUCER_LOCK.json'),
        append_source_modules=859, base_source_modules=1412, combined_source_modules=2271,
        append_theorem_roots=3262, combined_distinct_theorem_roots=len(audits), records=records,
        audits=audits, elapsed_seconds=time.monotonic() - start,
        source_built_same_pipeline_application_object_inputs=1412, outside_application_object_inputs=[],
        full_program_source_first_PV=False, combined_fresh_replay_completed=True,
        namespace_isolated=False, qualification=lock['qualification'])
    atomic(out / 'RECEIPT.json', result)
    print(json.dumps({k: result[k] for k in ['status', 'append_source_modules',
        'combined_source_modules', 'combined_distinct_theorem_roots', 'elapsed_seconds']}))

if __name__ == '__main__':
    main()
