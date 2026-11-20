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
import signal
import sys
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

from rebuild_qrh_closure import imports
from execute_demand_high_resource import DiskMeter

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


def validate(directory, result_name='RESULT.json'):
    result = strict_json(directory / result_name)
    need(result['status'] == 'FRESH_SELECTED_SOURCE_CLOSURE_PASS', 'complete replay status')
    need(result['old_application_objects_used'] is False, 'no old application objects')
    plan = strict_json(directory / 'PLAN.json')
    need(sha(directory / 'PLAN.json') == result['plan_sha256'], 'complete plan identity')
    need(sha(directory/'controller.py') == plan['script_sha256'] == sha(__file__), 'exact current guarded controller')
    need(sha(S/'scripts/execute_demand_high_resource.py') == plan['disk_helper_sha256'], 'exact frozen disk helper')
    need(plan['host_reserve_bytes'] >= 512 * 1024**3 and plan['min_available_bytes'] == 1024**4, 'live RAM policy')
    need(plan['scratch_forecast_bytes'] == 3 * 1024**3 and plan['scratch_ceiling_bytes'] == 300 * 1024**3, 'separate fixed disk policy')
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
    need(result['all_started_workers_drained'] is True, 'all actual workers drained')
    need(sha(directory/'RESOURCE_OBSERVATIONS.jsonl') == result['resource_observations_sha256'], 'actual live resource observations')
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
            need(type(event['memavailable_bytes']) is int and event['memavailable_bytes'] >= max(1024**4, plan['host_reserve_bytes'] + sum(reserved.values())), 'actual live RAM at every dispatch')
            space = event['disk']
            need(space['root'] == plan['owned_scratch_root'] and space['error'] is None and space['free_bytes'] >= 1024**4 and space['forecast_bytes'] == plan['scratch_forecast_bytes'] and space['allocated_bytes'] + space['forecast_bytes'] <= plan['scratch_ceiling_bytes'], 'actual independent free disk and owned scratch headroom at dispatch')
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
            'axioms': axioms, 'result_sha256': sha(directory / result_name)}


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
    parser.add_argument('--owned-scratch-root', type=Path)
    args = parser.parse_args()
    if args.check is not None:
        need(args.out is None and not args.root and not args.theorem and not args.application_source_root
             and not args.plan_only, 'check is a separate read-only mode')
        print(json.dumps(validate(args.check.resolve()), sort_keys=True))
        return
    need(args.out is not None, 'fresh --out required')
    out = args.out.resolve()
    need(not out.exists() and out.parent.is_dir(), 'fresh replay output; existing parent required')
    owned = Path(strict_json(S/'BUILD_CONTEXT.json')['new_application_object_root']).resolve().parent
    need(out.is_relative_to(owned) and out != owned, 'fresh output inside entire owned experiment')
    need(args.owned_scratch_root is None or args.owned_scratch_root.resolve() == owned, 'exact entire experiment scratch root')
    disk = DiskMeter(owned, 3 * 1024**3)
    initial_disk = disk.measure(True)
    need(disk.okay(initial_disk), 'separate genuinely1TiB free disk and300GiB total owned scratch with3GiB forecast')
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
    need(512 <= args.host_reserve_gib <= 4096, 'at least512GiB host reserve')
    host_reserve = args.host_reserve_gib << 30
    need(available >= 1024**4, 'guarded run requires genuinely available1TiB RAM')
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
            'min_available_bytes': 1024**4, 'owned_scratch_root': str(owned),
            'scratch_forecast_bytes': 3 * 1024**3, 'scratch_ceiling_bytes': 300 * 1024**3,
            'initial_disk': initial_disk, 'disk_helper_sha256': sha(S/'scripts/execute_demand_high_resource.py'),
            'python_optimization': sys.flags.optimize,
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
    failures = []
    drain = []
    resource_pauses = []
    resource_state = {'paused':False}
    def on_signal(sig, frame):
        drain.append(signal.Signals(sig).name)
    for sig in [signal.SIGUSR1, signal.SIGTERM, signal.SIGINT]:
        signal.signal(sig, on_signal)
    def memory_available():
        return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))) * 1024
    def resources(reserved, new_cap=0):
        memory = memory_available()
        space = disk.measure(force=new_cap > 0)
        okay = memory >= max(1024**4, host_reserve + reserved + new_cap) and disk.okay(space)
        row = dict(time_unix=time.time(), memavailable_bytes=memory, reserved_bytes=reserved, next_cap_bytes=new_cap, disk=space, dispatch_allowed=okay)
        with (out/'RESOURCE_OBSERVATIONS.jsonl').open('a') as stream:
            stream.write(json.dumps(row, allow_nan=False)+'\n')
        resource_state['paused'] = not okay
        if not okay:
            resource_pauses.append(row)
        return okay, row
    def journal(event):
        with (out/'SCHEDULE.jsonl').open('a') as stream:
            stream.write(json.dumps(event, allow_nan=False)+'\n')
    def checkpoint(running):
        atomic(out/'RUN_STATE.json',dict(status='ACTIVE_OR_DRAINED_NOT_ACCEPTANCE',completed=len(completed),total=len(order)+1,active=list(running.values()),failures=failures,drain_requests=drain,resource_paused=resource_state['paused']))
    def phase(specs):
        pending = {record['module']:record for record in specs}
        caps = {record['module']:record['memory_limit_bytes'] for record in specs}
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            running = {}
            while pending or running:
                reserved = sum(caps[name] for name in running.values())
                resources(reserved)
                if not drain and not failures:
                    for name,record in list(pending.items()):
                        if drain or failures or len(running) >= args.jobs:
                            break
                        if all(dependency not in modules or dependency in completed for dependency in record['imports']):
                            cap = record['memory_limit_bytes']
                            if reserved + cap > memory_total:
                                break
                            allowed,observed = resources(reserved,cap)
                            if not allowed or drain or failures:
                                break
                            journal(dict(event='reserve_before_submit',module=name,module_memory_limit_bytes=cap,running_caps_before_bytes=reserved,running_caps_after_bytes=reserved+cap,aggregate_ceiling_bytes=memory_total,memavailable_bytes=observed['memavailable_bytes'],disk=observed['disk']))
                            running[pool.submit(compile_one,record)] = name
                            reserved += cap
                            del pending[name]
                if not running:
                    checkpoint(running)
                    if drain or failures:
                        return False
                    need(any(all(dep not in modules or dep in completed for dep in r['imports']) for r in pending.values()),'acyclic source scheduling progress')
                    time.sleep(.5)
                    continue
                done,_ = wait(running,timeout=.5,return_when=FIRST_COMPLETED)
                for future in done:
                    name = running.pop(future)
                    try:
                        completed[name] = future.result()
                    except Exception as error:
                        failure = dict(module=name,error=repr(error),receipt=str(audit/name/'RUN.json'))
                        if (audit/name/'RUN.json').is_file():
                            failure['actual_receipt'] = strict_json(audit/name/'RUN.json')
                        failures.append(failure)
                    remaining = sum(caps[item] for item in running.values())
                    journal(dict(event='release_after_completion',module=name,module_memory_limit_bytes=caps[name],running_caps_after_bytes=remaining))
                checkpoint(running)
                if (drain or failures) and not running:
                    return False
        return True
    okay = phase(order)
    if okay:
        audit_source = out / 'source/RamanujanPV/SelectedReplayAudit.lean'
        audit_source.parent.mkdir(parents=True)
        audit_source.write_text(''.join('import '+target+'\n' for target in targets)+''.join('#print axioms '+name+'\n' for name in selected))
        final_record = dict(module='RamanujanPV.SelectedReplayAudit',source=str(audit_source),root=str(out/'source'),source_sha256=sha(audit_source),memory_limit_bytes=module_memory('RamanujanPV.SelectedReplayAudit'),imports=targets)
        okay = phase([final_record])
    if not okay:
        saved = dict(status='DRAINED_GUARDED_CHECKPOINT_NOT_ACCEPTANCE' if drain else 'FAILED_GUARDED_ATTEMPTS_NOT_ACCEPTANCE',plan_sha256=sha(out/'PLAN.json'),records=[completed[n] for n in [r['module'] for r in order]+['RamanujanPV.SelectedReplayAudit'] if n in completed],failures=failures,drain_requests=drain,remaining=[r['module'] for r in order if r['module'] not in completed],seconds=time.monotonic()-started,all_started_workers_drained=True)
        atomic(out/'CHECKPOINT.json',saved)
        print(json.dumps(dict(status=saved['status'],completed=len(completed),failed=len(failures))),flush=True)
        if failures:
            raise ValueError('failed attempts preserved after every active worker drained')
        return
    records = [completed[record['module']] for record in order]+[completed['RamanujanPV.SelectedReplayAudit']]
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
    result.update(resource_pause_samples=len(resource_pauses),all_started_workers_drained=True,actual_owned_disk_peak_bytes=disk.peak,final_disk=disk.measure(True),resource_observations_sha256=sha(out/'RESOURCE_OBSERVATIONS.jsonl'))
    atomic(out/'RESULT_CANDIDATE.json',result)
    validate(out,'RESULT_CANDIDATE.json')
    (out/'RESULT_CANDIDATE.json').replace(out/'RESULT.json')
    print(json.dumps(validate(out),sort_keys=True))


if __name__ == '__main__':
    main()
