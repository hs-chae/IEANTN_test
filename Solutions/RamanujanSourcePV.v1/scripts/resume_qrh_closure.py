#!/usr/bin/env python3
"""Continue a drained, source-locked fresh QRH closure without changing proofs.

Only fully successful, hash-checked source/object/receipt tuples are reused.
Partial attempts remain in the original directory. A fresh output contains
copies of all accepted earlier records plus every new compilation receipt.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import shutil
import signal
import subprocess
import threading
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

S = Path(__file__).resolve().parents[1]


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def atomic(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def available_memory():
    values = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().split('\n') if ':' in line)
    return int(values['MemAvailable'].split()[0]) * 1024


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--prior', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--cpus', default=','.join(str(i) for i in range(72, 84)))
    parser.add_argument('--jobs', type=int, default=12)
    parser.add_argument('--memory-gib', type=int, default=24)
    args = parser.parse_args()
    prior = args.prior.resolve()
    out = args.out.resolve()
    need(not out.exists(), 'fresh continuation output required')
    context_path = S / 'BUILD_CONTEXT.json'
    context = read(context_path)
    plan = read(prior / 'PLAN.json')
    need(plan['old_application_objects_used'] is False, 'fresh original application policy')
    need(sha(context_path) == plan['context_sha256'], 'build context changed')
    compiler = Path(context['compiler'])
    need(sha(compiler) == context['compiler_sha256'], 'compiler changed')
    drain = read(prior / 'DRAIN_COMPLETE.json')
    need(drain['status'] == 'ALL_OWNED_CHILDREN_EXITED_CONTROLLER_STOPPED_CLEANLY', 'old controller is not drained')
    pid_path = Path('/proc') / str(drain['controller_pid'])
    if pid_path.exists():
        need(pid_path.joinpath('stat').read_text().split()[2] == 'Z', 'old controller remains live')
    cpus = [int(value) for value in args.cpus.split(',')]
    need(len(cpus) == len(set(cpus)) and set(cpus) <= os.sched_getaffinity(0), 'available distinct CPUs')
    need(1 <= args.jobs <= len(cpus) <= 12, 'bounded coordinated worker count')
    need(1 <= args.memory_gib and args.jobs * args.memory_gib <= 300, '300 GiB aggregate ceiling')
    memory = args.memory_gib << 30
    reserve = 512 << 30
    need(available_memory() >= reserve + args.jobs * memory, 'host reserve before continuation')
    generic = []
    for dependency in context['generic_dependencies']:
        if not dependency['library_present']:
            continue
        root = Path(dependency['path'])
        need(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
             == dependency['revision'], 'generic pinned revision')
        need(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
             cwd=root, text=True), 'generic tracked source changed')
        generic.append(dependency['library'])
    need(generic == plan['generic_libraries'], 'generic libraries changed')
    modules = {row['module']: row for row in plan['ordered_modules']}
    order = [row['module'] for row in plan['ordered_modules']]
    need(len(modules) == len(order) == plan['module_count'], 'unique complete module plan')
    reused = {}
    partial = []
    for module in order:
        row = modules[module]
        need(sha(row['source']) == row['source_sha256'], 'source changed ' + module)
        directory = prior / 'audit' / module
        receipt = directory / 'RUN.json'
        if not receipt.exists():
            if directory.exists():
                partial.append(module)
            continue
        record = read(receipt)
        need(record['module'] == module and record['source'] == row['source'], 'prior receipt identity')
        need(record['source_sha256'] == row['source_sha256'], 'prior source hash')
        if record['exit_code'] != 0:
            partial.append(module)
            continue
        need(sha(directory / 'source.lean') == row['source_sha256'], 'prior source snapshot')
        for name in ['stdout', 'stderr', 'rusage']:
            need(sha(directory / name) == record[name + '_sha256'], 'prior output receipt')
        obj = prior / 'lean' / Path(*module.split('.')).with_suffix('.olean')
        need(sha(obj) == record['object_sha256'], 'prior object identity')
        reused[module] = record
    for module in reused:
        need(all(dep not in modules or dep in reused for dep in modules[module]['imports']),
             'reused object is missing a source-verified dependency')
    out.mkdir(parents=True)
    objects = out / 'lean'
    objects.mkdir()
    audit = out / 'audit'
    audit.mkdir()
    for module in reused:
        shutil.copytree(prior / 'audit' / module, audit / module)
        relative = Path(*module.split('.')).with_suffix('.olean')
        destination = objects / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(prior / 'lean' / relative, destination)
        need(sha(destination) == reused[module]['object_sha256'], 'copied object identity')
    continuation_plan = dict(plan)
    continuation_plan.update({
        'status': 'PLANNED_CHECKED_CONTINUATION',
        'application_object_root': str(objects), 'cpus': cpus,
        'max_parallel_workers': args.jobs, 'per_worker_memory_bytes': memory,
        'aggregate_worker_memory_ceiling_bytes': args.jobs * memory,
        'minimum_host_available_memory_reserve_bytes': reserve,
        'initial_available_memory_bytes': available_memory(),
        'prior_attempt': str(prior), 'prior_plan_sha256': sha(prior / 'PLAN.json'),
        'prior_drain_sha256': sha(prior / 'DRAIN_COMPLETE.json'),
        'reused_modules': list(reused), 'preserved_partial_prior_modules': partial,
        'continuation_script_sha256': sha(Path(__file__)),
        'continuation_command': [str(Path(__file__).resolve()), '--prior', str(prior),
                                 '--out', str(out), '--cpus', args.cpus,
                                 '--jobs', str(args.jobs), '--memory-gib', str(args.memory_gib)],
    })
    atomic(out / 'PLAN.json', continuation_plan)
    if (prior / 'SOURCE_NATIVE_SCAN.json').exists():
        shutil.copy2(prior / 'SOURCE_NATIVE_SCAN.json', out / 'SOURCE_NATIVE_SCAN.json')
    environment = dict(os.environ, LEAN_PATH=os.pathsep.join([str(objects), *generic]))
    live = {}
    live_lock = threading.Lock()
    stopping = threading.Event()

    def stop_jobs(signum, frame):
        stopping.set()
        with live_lock:
            pids = list(live)
            for pid in pids:
                try:
                    os.killpg(pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass
        atomic(out / 'INTERRUPTED.json', {'status': 'INTERRUPTED_OWNED_JOBS_TERMINATED',
                                         'signal': signum, 'process_groups': pids})
        raise KeyboardInterrupt

    signal.signal(signal.SIGINT, stop_jobs)
    signal.signal(signal.SIGTERM, stop_jobs)

    def compile_one(module, cpu):
        row = modules[module]
        source = Path(row['source'])
        need(sha(source) == row['source_sha256'], 'source changed before compile')
        directory = audit / module
        directory.mkdir()
        (directory / 'source.lean').write_bytes(source.read_bytes())
        obj = objects / Path(*module.split('.')).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = [str(compiler), '-j1', '-R', row['base'], str(source), '-o', str(obj)]
        full = ['/usr/bin/time', '-v', '-o', str(directory / 'rusage'),
                '/usr/bin/prlimit', '--as=' + str(memory), '--',
                '/usr/bin/taskset', '-c', str(cpu), *command]
        started = time.monotonic()
        with (directory / 'stdout').open('wb') as stdout, (directory / 'stderr').open('wb') as stderr:
            with live_lock:
                need(not stopping.is_set(), 'continuation is stopping')
                child = subprocess.Popen(full, cwd=row['base'], env=environment,
                                         stdout=stdout, stderr=stderr, start_new_session=True)
                live[child.pid] = module
            code = child.wait()
            with live_lock:
                live.pop(child.pid, None)
        need(sha(source) == row['source_sha256'], 'source changed during compile')
        record = dict(row, exit_code=code, seconds=time.monotonic() - started, cpu=cpu,
                      command=command, full_command=full,
                      stdout_sha256=sha(directory / 'stdout'),
                      stderr_sha256=sha(directory / 'stderr'),
                      rusage_sha256=sha(directory / 'rusage'))
        if code == 0:
            record['object_sha256'] = sha(obj)
        atomic(directory / 'RUN.json', record)
        return record

    completed = dict(reused)
    pending = set(order) - set(completed)
    running = {}
    started = time.monotonic()
    last = started
    print(json.dumps({'status': 'CONTINUATION_STARTED', 'reused': len(reused),
                      'pending': len(pending), 'workers': args.jobs}), flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        while pending or running:
            need(available_memory() >= reserve, 'host available memory reserve breached')
            free = [cpu for cpu in cpus[:args.jobs] if cpu not in running.values()]
            ready = [module for module in order if module in pending and
                     all(dep not in modules or dep in completed for dep in modules[module]['imports'])]
            for module, cpu in zip(ready, free):
                need(available_memory() >= reserve + memory, 'host reserve for new worker')
                pending.remove(module)
                running[pool.submit(compile_one, module, cpu)] = cpu
            need(running or not pending, 'blocked dependency graph')
            finished, _ = wait(running, timeout=20, return_when=FIRST_COMPLETED)
            for future in finished:
                running.pop(future)
                row = future.result()
                module = row['module']
                if row['exit_code'] != 0:
                    for other in running:
                        following = other.result()
                        if following['exit_code'] == 0:
                            completed[following['module']] = following
                    atomic(out / 'RESULT.json', {'status': 'FAILED_ATTEMPT_PRESERVED',
                         'failed': row, 'completed': list(completed), 'pending_count': len(pending),
                         'elapsed_seconds': time.monotonic() - started,
                         'old_application_objects_used': False})
                    print(json.dumps({'status': 'FAILED', 'module': module}), flush=True)
                    return 1
                completed[module] = row
            now = time.monotonic()
            if now - last >= 20 or not (pending or running):
                state = {'status': 'RUNNING' if pending or running else 'COMPILED',
                         'completed': len(completed), 'reused': len(reused), 'total': len(order),
                         'running': len(running), 'elapsed_seconds': now - started,
                         'available_memory_bytes': available_memory()}
                atomic(out / 'PROGRESS.json', state)
                print(json.dumps(state), flush=True)
                last = now
    atomic(out / 'RESULT.json', {'status': 'FRESH_QRH_CLOSURE_BUILD_PASS',
         'roots': plan['roots'], 'records': [completed[module] for module in order],
         'elapsed_seconds': time.monotonic() - started, 'reused_module_count': len(reused),
         'old_application_objects_used': False})
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
