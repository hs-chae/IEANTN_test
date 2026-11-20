#!/usr/bin/env python3
"""Fresh-source replay with bounded per-module address-space profiles.

Only pinned generic libraries are reused. Every application dependency is rebuilt
from its exact source, including optional accepted local-table proof sources.
There are no Python asserts or native Lean proof acceptance shortcuts.
"""
from pathlib import Path
import argparse
import hashlib
import json
import math
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


def strict_json_text(data):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    def invalid(value):
        raise ValueError('nonfinite JSON constant ' + value)
    def finite(value):
        parsed = float(value)
        need(math.isfinite(parsed), 'nonfinite JSON number')
        return parsed
    return json.loads(data, object_pairs_hook=pairs, parse_constant=invalid, parse_float=finite)


def strict_json(path):
    return strict_json_text(Path(path).read_text())


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
        expected_memory = (plan['final_audit_memory_limit_bytes'] if record['module'] == 'RamanujanPV.SelectedReplayAudit'
                           else next(m['memory_limit_bytes'] for m in plan['modules'] if m['module'] == record['module']))
        need(record['memory_limit_bytes'] == expected_memory, 'actual planned per-module resource cap')
    for payload in plan['payloads']:
        need(sha(payload['path']) == payload['sha256'], 'source payload identity')
    axioms = audit_axioms(Path(result['records'][-1]['stdout']).read_text(), plan['selected_theorems'])
    need(axioms == result['axioms'], 'actual final theorem dependency audit')
    schedule = directory / 'SCHEDULE.jsonl'
    need(schedule.is_file(), 'actual memory reservation journal')
    reserved = {}
    dispatched = set()
    record_caps = {record['module']: record['memory_limit_bytes'] for record in result['records']}
    for line in schedule.read_text().splitlines():
        event = strict_json_text(line)
        need(event['module'] in record_caps and type(event['module_memory_limit_bytes']) is int
             and event['module_memory_limit_bytes'] == record_caps[event['module']],
             'journal cap equals the actual planned/compiler cap')
        if event['event'] == 'reserve_before_submit':
            need(event['aggregate_ceiling_bytes'] == plan['aggregate_memory_ceiling_bytes'],
                 'same aggregate policy at actual dispatch')
            need(event['module'] not in reserved and event['module'] not in dispatched,
                 'unique actual submitted task')
            need(event['running_caps_before_bytes'] == sum(reserved.values()), 'actual prior reserved sum')
            reserved[event['module']] = event['module_memory_limit_bytes']
            dispatched.add(event['module'])
            need(event['running_caps_after_bytes'] == sum(reserved.values()) and
                 sum(reserved.values()) <= plan['aggregate_memory_ceiling_bytes'],
                 'every actual dispatch respected aggregate memory')
        else:
            need(event['event'] == 'release_after_completion' and event['module'] in reserved,
                 'actual completion releases an active reservation')
            need(reserved.pop(event['module']) == event['module_memory_limit_bytes'], 'same resource cap released')
            need(event['running_caps_after_bytes'] == sum(reserved.values()), 'actual post-release sum')
    need(not reserved and dispatched == {r['module'] for r in result['records']},
         'every planned module and final audit dispatched and completed exactly once')
    return {'status': 'CHECKED_COMPLETE_SELECTED_REPLAY', 'modules': len(plan['modules']),
            'axioms': axioms, 'result_sha256': sha(directory / 'RESULT.json')}


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--context', type=Path, default=S / 'BUILD_CONTEXT.json')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--root', action='append', default=[])
    parser.add_argument('--theorem', action='append', default=[])
    parser.add_argument('--memory-gib', type=int, default=48)
    parser.add_argument('--profile-json', type=Path)
    parser.add_argument('--aggregate-gib', type=int, default=300)
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
    profile = strict_json(args.profile_json) if args.profile_json else {'exact': {}, 'prefix': {}}
    need(set(profile) <= {'exact', 'prefix'}, 'known resource profile fields')
    exact = profile.get('exact', {})
    prefixes = profile.get('prefix', {})
    for mapping in [exact, prefixes]:
        need(type(mapping) is dict, 'resource profile mapping')
        for name, amount in mapping.items():
            need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', name) is not None,
                 'exact resource module/prefix identity')
            need(type(amount) is int and 1 <= amount <= 300, 'per-module resource ceiling')
    need(1 <= args.aggregate_gib <= 300, 'owner-authorized aggregate ceiling')
    memory_total = args.aggregate_gib << 30
    need(8 <= args.host_reserve_gib <= 4096, 'explicit adequate host reserve')
    host_reserve = args.host_reserve_gib << 30
    if memory_total > 48 << 30:
        need(available >= 1024**4, 'high-resource run requires genuinely available1TiB RAM')
    need(available >= host_reserve + memory_total, 'actual host reserve plus aggregate ceiling')
    def module_memory(name):
        amount = exact.get(name)
        if amount is None:
            matches = [(prefix, value) for prefix, value in prefixes.items()
                       if name == prefix or name.startswith(prefix + '.')]
            amount = max(matches, key=lambda pair: len(pair[0]))[1] if matches else args.memory_gib
        need(amount <= args.aggregate_gib, 'individual task fits aggregate ceiling')
        return amount << 30
    worker_memory = max([args.memory_gib, *exact.values(), *prefixes.values()]) << 30
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
                  'source_sha256': hashlib.sha256(before).hexdigest(), 'imports': dependencies,
                  'memory_limit_bytes': module_memory(module)}
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
            'resource_profile': profile, 'default_memory_gib': args.memory_gib,
            'final_audit_memory_limit_bytes': module_memory('RamanujanPV.SelectedReplayAudit'),
            'host_memavailable_before_bytes': available, 'cpus': sorted(cpus),
            'payloads': [{'path': p, 'sha256': h} for p, h in sorted(payloads.items())]}
    atomic(out / 'PLAN.json', plan)
    if args.plan_only:
        print(json.dumps({'status': 'PLANNED_EXACT_SELECTED_SOURCE_CLOSURE',
                          'modules': len(order), 'out': str(out)}, sort_keys=True))
        return
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(objects), *map(str, libraries)]))
    records = []
    started = time.monotonic()
    def compile_one(record):
        module = record['module']
        selected_memory = record['memory_limit_bytes']
        def limits():
            resource.setrlimit(resource.RLIMIT_AS, (selected_memory, selected_memory))
            os.sched_setaffinity(0, cpus)
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
                  'memory_limit_bytes': selected_memory,
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
                    reserved = sum(modules[active]['memory_limit_bytes'] for active in running.values())
                    if reserved + record['memory_limit_bytes'] > memory_total:
                        # Drain earlier work rather than starving this ready heavy module.
                        break
                    event = {'event': 'reserve_before_submit', 'module': name,
                             'module_memory_limit_bytes': record['memory_limit_bytes'],
                             'running_caps_before_bytes': reserved,
                             'running_caps_after_bytes': reserved + record['memory_limit_bytes'],
                             'aggregate_ceiling_bytes': memory_total}
                    with (out / 'SCHEDULE.jsonl').open('a') as journal:
                        journal.write(json.dumps(event, sort_keys=True) + '\n')
                    running[pool.submit(compile_one, record)] = name
                    del pending[name]
            need(bool(running), 'acyclic source dependency scheduling progress')
            done, _ = wait(running, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                completed[name] = future.result()
                reserved = sum(modules[active]['memory_limit_bytes'] for active in running.values())
                with (out / 'SCHEDULE.jsonl').open('a') as journal:
                    journal.write(json.dumps({'event': 'release_after_completion', 'module': name,
                        'module_memory_limit_bytes': modules[name]['memory_limit_bytes'],
                        'running_caps_after_bytes': reserved}, sort_keys=True) + '\n')
    records = [completed[record['module']] for record in order]
    audit_source = out / 'source/RamanujanPV/SelectedReplayAudit.lean'
    audit_source.parent.mkdir(parents=True)
    audit_source.write_text(''.join('import ' + target + '\n' for target in targets) +
                            ''.join('#print axioms ' + name + '\n' for name in selected))
    final_record = {'module': 'RamanujanPV.SelectedReplayAudit', 'source': str(audit_source),
                 'root': str(out / 'source'), 'source_sha256': sha(audit_source),
                 'memory_limit_bytes': module_memory('RamanujanPV.SelectedReplayAudit')}
    with (out / 'SCHEDULE.jsonl').open('a') as journal:
        journal.write(json.dumps({'event': 'reserve_before_submit', 'module': final_record['module'],
            'module_memory_limit_bytes': final_record['memory_limit_bytes'], 'running_caps_before_bytes': 0,
            'running_caps_after_bytes': final_record['memory_limit_bytes'],
            'aggregate_ceiling_bytes': memory_total}, sort_keys=True) + '\n')
    records.append(compile_one(final_record))
    with (out / 'SCHEDULE.jsonl').open('a') as journal:
        journal.write(json.dumps({'event': 'release_after_completion', 'module': final_record['module'],
            'module_memory_limit_bytes': final_record['memory_limit_bytes'],
            'running_caps_after_bytes': 0}, sort_keys=True) + '\n')
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
