#!/usr/bin/env python3
"""Fresh-source parallel replay of explicitly selected mathematical consumers.

Only pinned generic libraries are reused. Every application dependency is rebuilt
from its exact source, including optional accepted local-table proof sources.
There are no Python asserts or native Lean proof acceptance shortcuts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

from rebuild_qrh_closure import imports

S = Path(__file__).resolve().parents[1]
NETWORK = S.parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}



def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def strict_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def invalid(value):
        raise ValueError('nonfinite JSON constant ' + value)
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs, parse_constant=invalid)


def atomic(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def audit_axioms(text, names):
    result = {}
    for name in names:
        matches = re.findall("'" + re.escape(name) + r"' depends on axioms:\s*\[([^\]]*)\]", text)
        empty = re.findall("'" + re.escape(name) + r"' does not depend on any axioms", text)
        need(len(matches) + len(empty) == 1, 'exact actual axiom list for ' + name)
        axioms = [] if empty else [x.strip() for x in matches[0].split(',') if x.strip()]
        need(len(axioms) == len(set(axioms)) and set(axioms) <= STANDARD,
             'nonstandard execution/proof axiom in ' + name)
        result[name] = axioms
    return result


def validate(directory):
    result = strict_json(directory / 'RESULT.json')
    need(result['status'] == 'FRESH_SELECTED_SOURCE_CLOSURE_PASS', 'complete replay status')
    need(result['old_application_objects_used'] is False, 'no old application objects')
    plan = strict_json(directory / 'PLAN.json')
    need(sha(directory / 'PLAN.json') == result['plan_sha256'], 'complete plan identity')
    need(sha(plan['compiler']) == plan['compiler_sha256'], 'compiler identity')
    need(sha(plan['context']) == plan['context_sha256'], 'generic context identity')
    need(len(result['records']) == len(plan['modules']) + 1, 'all source modules plus final audit')
    for expected, record in zip(plan['modules'], result['records'][:-1], strict=True):
        need(expected['module'] == record['module'] and expected['source'] == record['source'],
             'ordered exact source closure')
        need(expected['source_sha256'] == record['source_sha256'], 'planned source bytes')
    for record in result['records']:
        need(type(record['exit_code']) is int and record['exit_code'] == 0, 'every actual compile succeeded')
        for field in ['source', 'object', 'stdout', 'stderr', 'rusage']:
            need(sha(record[field]) == record[field + '_sha256'], 'receipt/source/object drift: ' + field)
        need(record['source_unchanged_during_compile'] is True, 'source stable during compile')
    for payload in plan['payloads']:
        need(sha(payload['path']) == payload['sha256'], 'source payload identity')
    axioms = audit_axioms(Path(result['records'][-1]['stdout']).read_text(), plan['selected_theorems'])
    need(axioms == result['axioms'], 'actual final theorem dependency audit')
    return {'status': 'CHECKED_COMPLETE_SELECTED_REPLAY', 'modules': len(plan['modules']),
            'axioms': axioms, 'result_sha256': sha(directory / 'RESULT.json')}


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--context', type=Path, default=S / 'BUILD_CONTEXT.json')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--root', action='append', default=[])
    parser.add_argument('--theorem', action='append', default=[])
    parser.add_argument('--memory-gib', type=int, default=96)
    parser.add_argument('--host-reserve-gib', type=int, default=512)
    parser.add_argument('--application-source-root', type=Path, action='append', default=[])
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--plan-only', action='store_true')
    parser.add_argument('--cpus', default='8,9,10,11')
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    if args.check is not None:
        need(args.out is None and not args.root and not args.theorem and not args.application_source_root
             and not args.plan_only, 'check is a separate read-only mode')
        print(json.dumps(validate(args.check.resolve()), sort_keys=True))
        return
    need(args.out is not None, 'fresh --out required')
    out = args.out.resolve()
    need(not out.exists() and out.parent.is_dir(), 'fresh replay output; existing parent required')
    context = strict_json(args.context)
    compiler = Path(context['compiler'])
    need(sha(compiler) == context['compiler_sha256'], 'exact pinned compiler')
    libraries = []
    for dependency in context['generic_dependencies']:
        if not dependency['library_present']:
            continue
        root = Path(dependency['path'])
        need(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
             == dependency['revision'], 'generic dependency revision')
        need(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                         cwd=root, text=True), 'generic tracked source clean')
        library = Path(dependency['library'])
        need(library.is_dir(), 'generic library present')
        libraries.append(library)
    libraries.append(compiler.parent.parent / 'lib/lean')
    cpus = {int(x) for x in args.cpus.split(',')}
    need(0 < len(cpus) <= 64 and cpus <= os.sched_getaffinity(0), 'bounded actual CPU affinity')
    need(1 <= args.jobs <= len(cpus), 'parallel workers bounded by selected CPUs')
    available = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().split('\n')
                         if x.startswith('MemAvailable:'))) * 1024
    need(1 <= args.memory_gib <= 300, 'owner-authorized per-worker ceiling')
    worker_memory = args.memory_gib << 30
    memory_total = args.jobs * worker_memory
    need(8 <= args.host_reserve_gib <= 4096, 'explicit adequate host reserve')
    host_reserve = args.host_reserve_gib << 30
    need(memory_total <= 300 << 30, 'owner-authorized aggregate proof ceiling')
    if memory_total > 48 << 30:
        need(available >= 1024**4, 'parallel high-resource run requires genuinely available1TiB RAM')
    need(available >= host_reserve + memory_total, 'worker ceilings plus explicit actual host reserve')
    roots = [S, NETWORK]
    need(args.root and args.theorem, 'explicit selected module roots and theorem identities required')
    targets = args.root
    selected = args.theorem
    for name in targets + selected:
        need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', name) is not None,
             'exact simple Lean module/declaration identity')
    need(len(set(targets)) == len(targets) and len(set(selected)) == len(selected),
         'distinct selected roots and theorems')
    for root in args.application_source_root:
        root = root.resolve()
        need(root.is_dir() and root not in roots, 'distinct explicit application source root')
        roots.append(root)
    modules = {}
    visiting = set()
    order = []
    def visit(module):
        if module in modules:
            return
        relative = Path(*module.split('.')).with_suffix('.lean')
        candidates = [(root, root / relative) for root in roots if (root / relative).is_file()]
        if not candidates:
            need(any((library / relative.with_suffix('.olean')).is_file() for library in libraries),
                 'unresolved exact application import ' + module)
            return
        need(len(candidates) == 1, 'unambiguous source identity ' + module)
        root, source = candidates[0]
        need(module not in visiting, 'application import cycle')
        visiting.add(module)
        before = source.read_bytes()
        dependencies = imports(source)
        for dependency in dependencies:
            visit(dependency)
        visiting.remove(module)
        record = {'module': module, 'root': str(root), 'source': str(source),
                  'source_sha256': hashlib.sha256(before).hexdigest(), 'imports': dependencies}
        modules[module] = record
        order.append(record)
    for target in targets:
        visit(target)
    payloads = {}
    for module in order:
        source = Path(module['source'])
        for name in re.findall(r'include_str\s+"([^"]+)"', source.read_text()):
            payload = (source.parent / name).resolve()
            payloads[str(payload)] = sha(payload)
    out.mkdir()
    (out / 'controller.py').write_bytes(Path(__file__).read_bytes())
    (out / 'import-parser.py').write_bytes((S / 'scripts/rebuild_qrh_closure.py').read_bytes())
    objects = out / 'lean'
    objects.mkdir()
    audit = out / 'audit'
    audit.mkdir()
    plan = {'targets': targets, 'selected_theorems': selected, 'modules': order,
            'compiler': str(compiler), 'compiler_sha256': sha(compiler),
            'context': str(args.context.resolve()), 'context_sha256': sha(args.context),
            'script_sha256': sha(__file__), 'generic_libraries': [str(x) for x in libraries],
            'old_application_objects_used': False, 'max_parallel_workers': args.jobs,
            'aggregate_memory_ceiling_bytes': memory_total,
            'memory_ceiling_bytes': worker_memory, 'host_reserve_bytes': host_reserve,
            'host_memavailable_before_bytes': available, 'cpus': sorted(cpus),
            'payloads': [{'path': p, 'sha256': h} for p, h in sorted(payloads.items())]}
    atomic(out / 'PLAN.json', plan)
    if args.plan_only:
        print(json.dumps({'status': 'PLANNED_EXACT_SELECTED_SOURCE_CLOSURE',
                          'modules': len(order), 'out': str(out)}, sort_keys=True))
        return
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(objects), *map(str, libraries)]))
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (worker_memory, worker_memory))
        os.sched_setaffinity(0, cpus)
    records = []
    started = time.monotonic()
    def compile_one(record):
        module = record['module']
        source = Path(record['source'])
        need(sha(source) == record['source_sha256'], 'source changed since planning')
        receipt = audit / module
        receipt.mkdir()
        (receipt / 'source.lean').write_bytes(source.read_bytes())
        obj = objects / Path(*module.split('.')).with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        command = [str(compiler), '-j1', '-R', record['root'], str(source), '-o', str(obj)]
        t = time.monotonic()
        with (receipt / 'stdout').open('wb') as so, (receipt / 'stderr').open('wb') as se:
            run = subprocess.run(['/usr/bin/time', '-v', '-o', str(receipt / 'rusage'), *command],
                                 cwd=record['root'], env=env, preexec_fn=limits, stdout=so, stderr=se)
        rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', (receipt / 'rusage').read_text())
        need(rss is not None, 'actual peak RSS measurement')
        result = {'module': module, 'source': str(source), 'source_sha256': record['source_sha256'],
                  'source_unchanged_during_compile': sha(source) == record['source_sha256'],
                  'command': command, 'exit_code': run.returncode, 'seconds': time.monotonic() - t,
                  'peak_rss_bytes': int(rss.group(1)) * 1024,
                  'oom_or_sigkill_event': run.returncode in [-9, 137]}
        for field, path in [('object', obj), ('stdout', receipt / 'stdout'),
                            ('stderr', receipt / 'stderr'), ('rusage', receipt / 'rusage')]:
            result[field] = str(path)
            if path.is_file():
                result[field + '_sha256'] = sha(path)
        atomic(receipt / 'RUN.json', result)
        print(json.dumps({'module': module, 'exit_code': run.returncode,
                          'seconds': result['seconds']}, sort_keys=True), flush=True)
        need(run.returncode == 0 and result['source_unchanged_during_compile'],
             'actual Lean proof failed/source drift; partial attempt preserved')
        return result
    completed = {}
    pending = {record['module']: record for record in order}
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running = {}
        while pending or running:
            for name, record in list(pending.items()):
                if len(running) >= args.jobs:
                    break
                if all(dependency not in modules or dependency in completed for dependency in record['imports']):
                    running[pool.submit(compile_one, record)] = name
                    del pending[name]
            need(bool(running), 'acyclic source dependency scheduling progress')
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                completed[name] = future.result()
    records = [completed[record['module']] for record in order]
    audit_source = out / 'source/RamanujanPV/SelectedReplayAudit.lean'
    audit_source.parent.mkdir(parents=True)
    audit_source.write_text(''.join('import ' + target + '\n' for target in targets) +
                            ''.join('#print axioms ' + name + '\n' for name in selected))
    records.append(compile_one({'module': 'RamanujanPV.SelectedReplayAudit', 'source': str(audit_source),
                 'root': str(out / 'source'), 'source_sha256': sha(audit_source)}))
    axioms = audit_axioms(Path(records[-1]['stdout']).read_text(), selected)
    for record in records:
        need(sha(record['source']) == record['source_sha256'], 'final source identity')
    for payload in plan['payloads']:
        need(sha(payload['path']) == payload['sha256'], 'final include_str source identity')
    result = {'status': 'FRESH_SELECTED_SOURCE_CLOSURE_PASS',
              'plan_sha256': sha(out / 'PLAN.json'), 'old_application_objects_used': False,
              'seconds': time.monotonic() - started,
              'actual_peak_worker_rss_bytes': max(r['peak_rss_bytes'] for r in records),
              'actual_replay_disk_bytes': sum(p.stat().st_size for p in out.rglob('*') if p.is_file()),
              'oom_events': sum(r['oom_or_sigkill_event'] for r in records),
              'axioms': axioms, 'records': records,
              'physical_native_association_claimed': False}
    atomic(out / 'RESULT.json', result)
    print(json.dumps(validate(out), sort_keys=True))


if __name__ == '__main__':
    main()
