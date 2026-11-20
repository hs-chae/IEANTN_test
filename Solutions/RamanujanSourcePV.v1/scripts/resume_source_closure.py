#!/usr/bin/env python3
"""Continue an interrupted fresh-source replay after complete exact readback.

This never treats arbitrary old application objects as proof evidence. Every
reused object must have its original successful compiler/source/hash receipt in
the same originally fresh run. Partial attempts and interrupted objects remain
preserved. SIGUSR1/SIGTERM/SIGINT drain current modules without launching more.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import resource
import signal
import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

S = Path(__file__).resolve().parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs)


def atomic(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--run-root', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--memory-gib', type=int, default=48)
    parser.add_argument('--cpus', default='72,73,74,75,76,77')
    parser.add_argument('--host-reserve-gib', type=int, default=512)
    args = parser.parse_args()
    run_root = args.run_root.resolve()
    out = args.out.resolve()
    need(run_root.is_dir() and not (run_root / 'RESULT.json').exists(), 'unfinished original replay')
    need(out.is_relative_to(run_root) and not out.exists(), 'fresh owned additive continuation')
    plan_path = run_root / 'PLAN.json'
    plan = read_json(plan_path)
    compiler = Path(plan['compiler'])
    need(sha(compiler) == plan['compiler_sha256'], 'original pinned compiler')
    need(sha(plan['context']) == plan['context_sha256'], 'original pinned generic context')
    context = read_json(plan['context'])
    for dependency in context['generic_dependencies']:
        if not dependency['library_present']:
            continue
        location = Path(dependency['path'])
        need(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=location, text=True).strip()
             == dependency['revision'], 'generic source revision')
        need(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                         cwd=location, text=True), 'generic tracked-source identity')
    cpus = {int(x) for x in args.cpus.split(',')}
    need(0 < len(cpus) <= 64 and cpus <= os.sched_getaffinity(0), 'actual allowed CPU set')
    need(1 <= args.jobs <= len(cpus) and 1 <= args.memory_gib <= 300, 'bounded worker resources')
    worker_memory = args.memory_gib << 30
    aggregate = worker_memory * args.jobs
    need(aggregate <= 300 << 30, 'owner-authorized aggregate continuation ceiling')
    available = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().split('\n')
                         if x.startswith('MemAvailable:'))) * 1024
    need(8 <= args.host_reserve_gib <= 4096, 'explicit adequate host reserve')
    reserve = args.host_reserve_gib << 30
    need(available >= reserve + aggregate, 'actual RAM plus preserved host reserve')
    if aggregate > 48 << 30:
        need(available >= 1024**4, 'high-resource authorization requires genuine available1TiB RAM')
    modules = {entry['module']: entry for entry in plan['modules']}
    need(len(modules) == len(plan['modules']), 'distinct original module identities')
    for entry in plan['modules']:
        need(sha(entry['source']) == entry['source_sha256'], 'unchanged fixed mathematical source ' + entry['module'])
    for payload in plan['payloads']:
        need(sha(payload['path']) == payload['sha256'], 'unchanged actual C source payload')
    objects = run_root / 'lean'
    completed = {}
    receipt_sources = {}
    candidates = list((run_root / 'audit').glob('*/RUN.json'))
    candidates += [p for p in run_root.glob('resume-*/audit/*/RUN.json') if p.parent.name in modules]
    for path in sorted(candidates):
        record = read_json(path)
        name = record['module']
        if name not in modules or record.get('exit_code') != 0:
            continue
        expected = modules[name]
        need(record['source'] == expected['source'] and record['source_sha256'] == expected['source_sha256'],
             'successful original receipt must match exact selected source')
        need(record['source_unchanged_during_compile'] is True, 'stable source during original compile')
        expected_object = objects / Path(*name.split('.')).with_suffix('.olean')
        need(Path(record['object']).resolve() == expected_object.resolve(), 'same original fresh object bank')
        need(record['command'] == [str(compiler), '-j1', '-R', expected['root'], expected['source'],
                                    '-o', str(expected_object)], 'actual original compiler invocation')
        for field in ['source', 'object', 'stdout', 'stderr', 'rusage']:
            need(sha(record[field]) == record[field + '_sha256'], 'exact successful original artifact ' + field)
        need(sha(path.parent / 'source.lean') == expected['source_sha256'], 'original source snapshot')
        if name in completed:
            need(completed[name]['object_sha256'] == record['object_sha256'], 'nondivergent reused proof object')
        completed[name] = record
        receipt_sources[name] = {'receipt': str(path), 'receipt_sha256': sha(path)}
    for name in completed:
        need(all(dependency not in modules or dependency in completed for dependency in modules[name]['imports']),
             'successful receipt import closure is complete')
    out.mkdir()
    (out / 'controller.py').write_bytes(Path(__file__).read_bytes())
    audit = out / 'audit'
    audit.mkdir()
    quarantine = out / 'unaccepted-preexisting-objects'
    moved = []
    for name, entry in modules.items():
        obj = objects / Path(*name.split('.')).with_suffix('.olean')
        if name not in completed and obj.exists():
            destination = quarantine / obj.relative_to(objects)
            destination.parent.mkdir(parents=True, exist_ok=True)
            moved.append({'module': name, 'original': str(obj), 'preserved': str(destination), 'sha256': sha(obj)})
            obj.rename(destination)
    continuation = {'status': 'EXACT_READBACK_CONTINUATION_STARTED', 'original_run_root': str(run_root),
                    'original_plan_sha256': sha(plan_path), 'controller_sha256': sha(__file__),
                    'reused_count': len(completed), 'reused_successful_receipts': receipt_sources,
                    'quarantined_unaccepted_objects': moved,
                    'worker_memory_ceiling_bytes': worker_memory, 'max_workers': args.jobs,
                    'aggregate_worker_memory_ceiling_bytes': aggregate, 'host_reserve_bytes': reserve,
                    'host_memavailable_before_bytes': available, 'cpus': sorted(cpus),
                    'same_fixed_sources_parameters_and_math': True,
                    'old_application_objects_outside_this_fresh_run_used': False}
    atomic(out / 'READBACK.json', continuation)
    stopping = threading.Event()
    reasons = []
    def drain(signum, frame):
        reasons.append(signal.Signals(signum).name)
        stopping.set()
    for signum in [signal.SIGUSR1, signal.SIGTERM, signal.SIGINT]:
        signal.signal(signum, drain)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(objects), *plan['generic_libraries']]))
    lock = threading.Lock()
    children = {}
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (worker_memory, worker_memory))
        os.sched_setaffinity(0, cpus)
    def compile_one(entry):
        name = entry['module']
        source = Path(entry['source'])
        need(sha(source) == entry['source_sha256'], 'source unchanged before continued compile')
        leaf = audit / name
        leaf.mkdir()
        (leaf / 'source.lean').write_bytes(source.read_bytes())
        obj = objects / Path(*name.split('.')).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = [str(compiler), '-j1', '-R', entry['root'], str(source), '-o', str(obj)]
        started = time.monotonic()
        with (leaf / 'stdout').open('wb') as so, (leaf / 'stderr').open('wb') as se:
            child = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(leaf / 'rusage'), *command],
                                     cwd=entry['root'], env=env, preexec_fn=limits, stdout=so, stderr=se)
            with lock:
                children[name] = child.pid
            returncode = child.wait()
            with lock:
                children.pop(name)
        usage = (leaf / 'rusage').read_text()
        rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', usage)
        need(rss is not None, 'actual continued worker peak RAM')
        record = {'module': name, 'source': str(source), 'source_sha256': entry['source_sha256'],
                  'source_unchanged_during_compile': sha(source) == entry['source_sha256'],
                  'command': command, 'exit_code': returncode, 'seconds': time.monotonic() - started,
                  'peak_rss_bytes': int(rss.group(1)) * 1024,
                  'oom_or_sigkill_event': returncode in [-9, 137],
                  'worker_memory_ceiling_bytes': worker_memory}
        for field, path in [('object', obj), ('stdout', leaf / 'stdout'), ('stderr', leaf / 'stderr'),
                            ('rusage', leaf / 'rusage')]:
            record[field] = str(path)
            if path.is_file():
                record[field + '_sha256'] = sha(path)
        atomic(leaf / 'RUN.json', record)
        print(json.dumps({'module': name, 'exit_code': returncode, 'seconds': record['seconds']}, sort_keys=True),
              flush=True)
        need(returncode == 0 and record['source_unchanged_during_compile'],
             'continued proof failed/source drift; exact failed attempt preserved')
        return record
    pending = {name: entry for name, entry in modules.items() if name not in completed}
    started = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running = {}
        while pending or running:
            if not stopping.is_set():
                for name, entry in list(pending.items()):
                    if len(running) >= args.jobs:
                        break
                    if all(dep not in modules or dep in completed for dep in entry['imports']):
                        running[pool.submit(compile_one, entry)] = name
                        del pending[name]
            with lock:
                live = dict(children)
            atomic(out / 'RUN_STATE.json', {'controller_pid': os.getpid(), 'updated_unix_seconds': time.time(),
                'completed': len(completed), 'pending': len(pending), 'running_modules': list(running.values()),
                'observed_child_pids': live, 'drain_requested': stopping.is_set(), 'drain_signals': reasons})
            if not running:
                need(stopping.is_set() or not pending, 'source dependency scheduler progress')
                break
            done, _ = wait(running, timeout=5, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                try:
                    completed[name] = future.result()
                except Exception:
                    stopping.set()
                    reasons.append('EXACT_WORKER_FAILURE')
                    raise
    if pending:
        atomic(out / 'DRAINED.json', {'status': 'DRAINED_AT_COMPLETED_MODULE_BOUNDARY',
            'completed': len(completed), 'pending': len(pending), 'running': [], 'reasons': reasons})
        return
    records = [completed[entry['module']] for entry in plan['modules']]
    source = out / 'source/RamanujanPV/SegmentReplayAudit.lean'
    source.parent.mkdir(parents=True)
    source.write_text(''.join('import ' + name + '\n' for name in plan['targets']) +
                      ''.join('#print axioms ' + name + '\n' for name in plan['selected_theorems']))
    final = compile_one({'module': 'RamanujanPV.SegmentReplayAudit', 'source': str(source),
                         'root': str(out / 'source'), 'source_sha256': sha(source)})
    records.append(final)
    text = Path(final['stdout']).read_text()
    axioms = {}
    for name in plan['selected_theorems']:
        lists = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", text)
        empty = re.findall("'" + re.escape(name) + r"' does not depend on any axioms", text)
        need(len(lists) + len(empty) == 1, 'exact actual selected theorem axiom report')
        row = [] if empty else [x.strip() for x in lists[0].split(',') if x.strip()]
        need(set(row) <= STANDARD, 'no new/native proof axioms')
        axioms[name] = row
    for record in records:
        need(sha(record['source']) == record['source_sha256'], 'final fixed source readback')
        need(sha(record['object']) == record['object_sha256'], 'final accepted proof object readback')
    for payload in plan['payloads']:
        need(sha(payload['path']) == payload['sha256'], 'final actual source payload readback')
    result = {'status': 'FRESH_SEGMENT_CHECKER_SOURCE_CLOSURE_PASS', 'plan_sha256': sha(plan_path),
              'old_application_objects_used': False, 'same_fresh_run_checked_resume': str(out),
              'resumed_count': continuation['reused_count'], 'seconds_this_continuation': time.monotonic() - started,
              'actual_peak_worker_rss_bytes': max(row['peak_rss_bytes'] for row in records),
              'aggregate_peak_RAM_not_measured_by_this_receipt': True,
              'oom_events': sum(row['oom_or_sigkill_event'] for row in records),
              'axioms': axioms, 'records': records,
              'physical_native_caller_proved': False, 'full_prefix_to_1490000000000_verified': False}
    atomic(out / 'RESULT.json', result)
    atomic(run_root / 'RESULT.json', result)
    print(json.dumps({'status': result['status'], 'completed': len(modules),
                      'resumed_count': continuation['reused_count'], 'result_sha256': sha(run_root / 'RESULT.json')}))


if __name__ == '__main__':
    main()
