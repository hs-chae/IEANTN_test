#!/usr/bin/env python3
"""Rebuild the selected transitive application-source closure in a fresh directory.

Only pinned generic Lean/Mathlib package objects are reused. Application sources
are copied and hashed before compilation; no predecessor application object path
is put on LEAN_PATH. This is kernel verification, not source-first PV.
"""
import argparse
import csv
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path):
    answer = []
    for line in path.read_text().split('\n'):
        if line.startswith('import '):
            answer.extend(line[7:].split('--', 1)[0].split())
    return answer


def tree_rss(pid):
    todo, seen, total = [pid], set(), 0
    while todo:
        current = todo.pop()
        if current in seen:
            continue
        seen.add(current)
        try:
            status = Path('/proc', str(current), 'status').read_text()
            match = re.search(r'^VmRSS:\s+(\d+) kB$', status, re.M)
            if match:
                total += int(match.group(1)) * 1024
            for task in Path('/proc', str(current), 'task').iterdir():
                try:
                    todo.extend(map(int, (task / 'children').read_text().split()))
                except (FileNotFoundError, ProcessLookupError):
                    pass
        except (FileNotFoundError, ProcessLookupError):
            pass
    return total


def main():
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    parser.add_argument('--repository', type=Path, required=True)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--roots', nargs='+', required=True)
    parser.add_argument('--source-dir', action='append', type=Path, default=[])
    parser.add_argument('--module-file', action='append', default=[], metavar='MODULE=PATH')
    parser.add_argument('--include-core', action='store_true')
    parser.add_argument('--jobs', type=int, default=4)
    parser.add_argument('--generic-lean-path')
    parser.add_argument('--compiler', type=Path)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 4:
        raise SystemExit('Supported bounded worker count is 1..4')
    repo = args.repository.resolve(strict=True)
    here = Path(__file__).resolve().parent
    context = json.loads((here / 'LOCAL_CONTEXT.json').read_text())
    compiler = (args.compiler or Path(context['compiler'])).resolve(strict=True)
    generic = args.generic_lean_path or context['mathlib_lean_path']
    generic_paths = [p for p in generic.split(':')
                     if '/.lake/packages/' in p or '/toolchains/' in p]
    if not generic_paths:
        raise SystemExit('No pinned generic package paths')
    registry = {}
    for row in json.loads((here / 'BASELINE_IMPORTS.json').read_text())['modules']:
        path = repo / row['captured_path']
        if sha(path) != row['sha256']:
            raise SystemExit('Baseline source mismatch: ' + row['module'])
        registry[row['module']] = path
    if args.include_core:
        for path in (repo / 'IEANTN').rglob('*.lean'):
            if path.name == 'Challenge.lean':
                continue
            module = '.'.join(path.relative_to(repo).with_suffix('').parts)
            if module in registry and sha(path) != sha(registry[module]):
                raise SystemExit('Core source differs from frozen predecessor: ' + module)
            registry[module] = path
    for folder in args.source_dir:
        for path in folder.resolve(strict=True).glob('*.lean'):
            if path.stem in registry:
                raise SystemExit('Duplicate compiler module: ' + path.stem)
            registry[path.stem] = path
    for item in args.module_file:
        module, separator, filename = item.partition('=')
        if not separator or module in registry:
            raise SystemExit('Invalid or duplicate explicit module: ' + item)
        registry[module] = Path(filename).resolve(strict=True)
    order, deps, visiting, visited = [], {}, set(), set()

    def visit(module):
        if module in visited:
            return
        if module in visiting:
            raise SystemExit('Import cycle: ' + module)
        if module not in registry:
            generic_prefixes = ('Mathlib', 'Lean', 'Init', 'Std', 'Aesop', 'Batteries', 'Qq')
            if any(module == p or module.startswith(p + '.') for p in generic_prefixes):
                return
            raise SystemExit('Application provider missing: ' + module)
        visiting.add(module)
        deps[module] = imports(registry[module])
        for dependency in deps[module]:
            visit(dependency)
        visiting.remove(module)
        visited.add(module)
        order.append(module)

    for root in args.roots:
        visit(root)
    run = args.run.resolve()
    if run.exists():
        raise SystemExit('Run directory must be fresh')
    source, objects, logs = run / 'source', run / 'objects', run / 'logs'
    for directory in (source, objects, logs):
        directory.mkdir(parents=True)
    controller = run / 'rebuild_closure.executed.py'
    controller.write_bytes(Path(__file__).read_bytes())
    (run / 'BASELINE_IMPORTS.executed.json').write_bytes((here / 'BASELINE_IMPORTS.json').read_bytes())
    (run / 'LOCAL_CONTEXT.executed.json').write_bytes((here / 'LOCAL_CONTEXT.json').read_bytes())
    source_rows = []
    for module in order:
        destination = source / (module.replace('.', '/') + '.lean')
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(registry[module].read_bytes())
        source_rows.append({'module': module, 'source_sha256': sha(destination),
                            'origin': str(registry[module]),
                            'executed': str(destination), 'imports': deps[module]})
    plan = {'status': 'FROZEN_SOURCE_PLAN_NOT_ACCEPTANCE', 'roots': args.roots,
            'modules': source_rows, 'compiler': str(compiler),
            'compiler_sha256': sha(compiler), 'jobs': args.jobs,
            'controller_sha256': sha(controller),
            'BASELINE_IMPORTS_sha256': sha(run / 'BASELINE_IMPORTS.executed.json'),
            'LOCAL_CONTEXT_sha256': sha(run / 'LOCAL_CONTEXT.executed.json'),
            'per_process_AS_bytes': 64 * 1024**3,
            'generic_paths': generic_paths, 'predecessor_application_objects_used': False,
            'host_meminfo': Path('/proc/meminfo').read_text(),
            'scope': 'Selected transitive kernel proof closure; no new source-first PV.'}
    (run / 'PLAN.json').write_text(json.dumps(plan, indent=2) + '\n')
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(objects)] + generic_paths)
    start, sample_time, peak = time.monotonic(), 0, 0
    waiting, active, finished, builds = order.copy(), {}, set(), []
    failure = None
    with (run / 'TREE_RSS.csv').open('w', newline='') as stream:
        samples = csv.writer(stream)
        samples.writerow(['elapsed_seconds', 'sampled_owned_tree_RSS_bytes', 'active_compilers'])
        while waiting or active:
            for module in waiting.copy():
                if failure or len(active) >= args.jobs:
                    break
                if not all(d in finished for d in deps[module] if d in visited):
                    continue
                available = int(re.search(r'MemAvailable:\s+(\d+)', Path('/proc/meminfo').read_text())[1]) * 1024
                if available < 256 * 1024**3:
                    failure = 'Host available memory below admission reserve'
                    break
                path = source / (module.replace('.', '/') + '.lean')
                obj = objects / (module.replace('.', '/') + '.olean')
                obj.parent.mkdir(parents=True, exist_ok=True)
                stdout = (logs / (module + '.stdout')).open('wb')
                stderr = (logs / (module + '.stderr')).open('wb')
                command = ['/usr/bin/prlimit', '--as=68719476736', '--', '/usr/bin/time', '-v',
                           str(compiler), '--root=' + str(source), '-j2', '-o', str(obj), str(path)]
                process = subprocess.Popen(command, env=env, stdout=stdout, stderr=stderr)
                active[module] = (process, stdout, stderr, command, time.monotonic())
                waiting.remove(module)
            for module, item in list(active.items()):
                process, stdout, stderr, command, began = item
                status = process.poll()
                if status is None:
                    continue
                stdout.close()
                stderr.close()
                obj = objects / (module.replace('.', '/') + '.olean')
                error_text = (logs / (module + '.stderr')).read_text()
                rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', error_text)
                builds.append({'module': module, 'returncode': status, 'command': command,
                               'seconds': time.monotonic() - began,
                               'peak_child_RSS_KiB': int(rss[1]) if rss else None,
                               'stdout_sha256': sha(logs / (module + '.stdout')),
                               'stderr_sha256': sha(logs / (module + '.stderr')),
                               'object_sha256': sha(obj) if obj.exists() else None})
                del active[module]
                if status or not obj.exists():
                    failure = 'Compiler failure: ' + module
                else:
                    finished.add(module)
                (run / 'PROGRESS.json').write_text(json.dumps({'finished': len(finished),
                    'total': len(order), 'active': list(active), 'failure': failure}) + '\n')
            now = time.monotonic()
            if now - sample_time >= 1:
                observed = tree_rss(os.getpid())
                peak = max(peak, observed)
                samples.writerow([now - start, observed, len(active)])
                stream.flush()
                sample_time = now
            if failure and not active:
                break
            time.sleep(.1)
    files = [p for p in run.rglob('*') if p.is_file()]
    receipt = {'status': 'FAILED' if failure else 'PASS_FRESH_TRANSITIVE_COMPILATION',
               'failure': failure, 'roots': args.roots, 'compiled_modules': len(finished),
               'required_modules': len(order), 'seconds': time.monotonic() - start,
               'sampled_peak_owned_tree_RSS_bytes': peak,
               'peak_individual_child_RSS_KiB': max((b['peak_child_RSS_KiB'] or 0 for b in builds), default=0),
               'owned_allocated_disk_bytes': sum(p.stat().st_blocks * 512 for p in files),
               'observed_SIGKILL_compiler_events': sum(b['returncode'] in (-9, 137) for b in builds),
               'PLAN_sha256': sha(run / 'PLAN.json'), 'TREE_RSS_sha256': sha(run / 'TREE_RSS.csv'),
               'builds': builds,
               'limitation': 'Compilation receipt. Axiom, exact-type, source applicability and proof-value audits are separate gates.'}
    (run / 'EXECUTION.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: receipt[k] for k in ('status', 'compiled_modules', 'required_modules', 'seconds')}), flush=True)
    if failure:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
