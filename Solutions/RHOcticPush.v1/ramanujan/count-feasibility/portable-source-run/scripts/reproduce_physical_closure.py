#!/usr/bin/env python3
"""Resource-only physical-aware variant of the pinned fresh-source replay engine.

Compiler commands, numerical source discovery, mathematical checks and per-module
address-space profiles are preserved. Physical admission uses current owned RSS,
20% above completed peaks (at least39.6GiB for large ordinary workers), potential
active growth and a512GiB host reserve. At most22 workers are dispatched. A256GiB
profile is admitted alone with its whole ceiling reserved physically. The old
virtual-address aggregate is not described as a physical memory measurement.

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
import threading
import subprocess
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

from rebuild_qrh_closure import imports

S = Path(__file__).resolve().parents[1]
NETWORK = S.parents[1]
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

INITIAL_FORECAST=(198*(1<<30)+4)//5  # 39.6GiB, exact upward-rounded integer
HEAVY_THRESHOLD=256*(1<<30)

def physical_forecast(address_cap,completed_peak):
    need(type(address_cap) is int and address_cap>0 and type(completed_peak) is int
         and completed_peak>=0,'strict physical forecast inputs')
    if address_cap>=HEAVY_THRESHOLD:return address_cap
    return min(address_cap,max(INITIAL_FORECAST,(6*completed_peak+4)//5))

def mem_available():
    return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines()
                    if x.startswith('MemAvailable:')))*1024

def process_info(pid):
    try:
        root=Path('/proc')/str(pid)
        fields=(root/'stat').read_text().rsplit(')',1)[1].split()
        status=(root/'status').read_text().splitlines()
        rss=next((int(x.split()[1])*1024 for x in status if x.startswith('VmRSS:')),0)
        return {'start_ticks':fields[19],'RSS_bytes':rss,'state':fields[0]}
    except (FileNotFoundError,ProcessLookupError):return None

def owned_tree_rss(pid,start_ticks):
    root=process_info(pid)
    if root is None or root['start_ticks']!=start_ticks:return 0
    total=0;pending=[pid];seen=set()
    while pending:
        current=pending.pop()
        if current in seen:continue
        seen.add(current);row=process_info(current)
        if row is None:continue
        total+=row['RSS_bytes']
        try:
            children=Path('/proc')/str(current)/'task'/str(current)/'children'
            pending.extend(int(x) for x in children.read_text().split())
        except (FileNotFoundError,ProcessLookupError):pass
    return total

def validate_physical_journal(directory,plan,result):
    need(plan['resource_scheduler']==result['resource_scheduler']=='PHYSICAL_RSS_FORECAST_V1',
         'physical forecast scheduler identity')
    need(type(plan['max_parallel_workers']) is int and 1<=plan['max_parallel_workers']<=22,
         'bounded actual physical workers')
    need(type(plan['host_reserve_bytes']) is int and plan['host_reserve_bytes']>=512*(1<<30)
         and type(plan['per_task_address_space_ceiling_bytes']) is int
         and 0<plan['per_task_address_space_ceiling_bytes']<=300*(1<<30),
         'separate actual host reserve and per-task AS ceiling')
    need(type(plan['initial_physical_forecast_bytes']) is int
         and plan['initial_physical_forecast_bytes']==INITIAL_FORECAST
         and type(plan['completed_peak_safety_factor']) is list
         and all(type(x) is int for x in plan['completed_peak_safety_factor'])
         and plan['completed_peak_safety_factor']==[6,5]
         and type(plan['heavy_exclusive_address_threshold_bytes']) is int
         and plan['heavy_exclusive_address_threshold_bytes']==HEAVY_THRESHOLD,
         'exact RSS forecasting rule')
    records={x['module']:x for x in result['records']}
    need(len(records)==len(result['records']),'unique physical journal compiler population')
    need(all(type(x['peak_rss_bytes']) is int and x['peak_rss_bytes']>0 for x in records.values()),
         'strict measured child RSS values')
    caps={n:r['memory_limit_bytes'] for n,r in records.items()}
    need(all(type(v) is int and 0<v<=plan['per_task_address_space_ceiling_bytes'] for v in caps.values()),
         'strict individual AS limits')
    reserved={};dispatched=set();peak=0
    journal=directory/'SCHEDULE.jsonl'
    need(journal.is_file(),'actual physical admission journal')
    for line in journal.read_text().splitlines():
        event=strict_json_text(line);name=event['module']
        need(name in caps and type(event['module_address_limit_bytes']) is int
             and event['module_address_limit_bytes']==caps[name],'actual module AS limit')
        for field in ['running_workers_after','running_address_limits_after_bytes']:
            need(type(event[field]) is int and event[field]>=0,'strict physical journal counter')
        if event['event']=='reserve_before_submit':
            need(name not in reserved and name not in dispatched,'unique actual dispatch')
            need(type(event['running_workers_before']) is int
                 and event['running_workers_before']==len(reserved)
                 and type(event['running_address_limits_before_bytes']) is int
                 and event['running_address_limits_before_bytes']==sum(reserved.values()),
                 'actual prior worker and virtual-address totals')
            snapshots=event['active']
            need(type(snapshots) is list and len(snapshots)==len(reserved)
                 and {q['module']for q in snapshots}==set(reserved),'all active worker observations')
            growth=0
            for row in snapshots:
                need(type(row['observed_RSS_bytes']) is int and row['observed_RSS_bytes']>=0
                     and type(row['physical_forecast_bytes']) is int
                     and row['physical_forecast_bytes']==physical_forecast(caps[row['module']],peak),
                     'actual RSS observations and learned forecasts')
                need(type(row['potential_growth_bytes']) is int
                     and row['potential_growth_bytes']==max(0,row['physical_forecast_bytes']-row['observed_RSS_bytes']),
                     'active potential physical growth')
                growth+=row['potential_growth_bytes']
            for field in ['physical_forecast_bytes','completed_peak_RSS_bytes','host_reserve_bytes',
                          'MemAvailable_bytes','active_potential_growth_bytes','required_available_bytes']:
                need(type(event[field]) is int and event[field]>=0,'strict physical admission metadata')
            need(event['completed_peak_RSS_bytes']==peak and
                 event['host_reserve_bytes']==plan['host_reserve_bytes'] and
                 event['physical_forecast_bytes']==physical_forecast(caps[name],peak) and
                 event['active_potential_growth_bytes']==growth and
                 event['required_available_bytes']==plan['host_reserve_bytes']+growth+event['physical_forecast_bytes']
                 and event['MemAvailable_bytes']>=event['required_available_bytes'],
                 'each actual admission preserves reserve plus potential growth')
            need(not any(c>=HEAVY_THRESHOLD for c in reserved.values())
                 and (caps[name]<HEAVY_THRESHOLD or not reserved),'heavy profiles run alone')
            reserved[name]=caps[name];dispatched.add(name)
            need(event['running_workers_after']==len(reserved)<=plan['max_parallel_workers']
                 and event['running_address_limits_after_bytes']==sum(reserved.values()),
                 'at most22 actual workers, AS sum informational only')
        else:
            need(event['event']=='release_after_completion' and name in reserved,'actual reservation release')
            need(type(event['actual_peak_RSS_bytes']) is int and
                 event['actual_peak_RSS_bytes']==records[name]['peak_rss_bytes'],'observed completed child peak')
            peak=max(peak,event['actual_peak_RSS_bytes'])
            need(type(event['completed_peak_RSS_bytes']) is int and event['completed_peak_RSS_bytes']==peak,
                 'updated actual completed RSS maximum')
            reserved.pop(name)
            need(event['running_workers_after']==len(reserved) and
                 event['running_address_limits_after_bytes']==sum(reserved.values()),'actual released totals')
    need(not reserved and dispatched==set(records),'complete actual dispatch and drain')
    need(sha(directory/'RESOURCE_SAMPLES.jsonl')==result['RESOURCE_SAMPLES_sha256'],
         'actual owned RSS sample log identity')
    samples=[strict_json_text(x)for x in (directory/'RESOURCE_SAMPLES.jsonl').read_text().splitlines()]
    need(samples,'nonempty actual owned RSS samples')
    for row in samples:
        need(type(row['MemAvailable_bytes']) is int and row['MemAvailable_bytes']>=0
             and type(row['owned_regular_disk_bytes']) is int
             and 0<=row['owned_regular_disk_bytes']<=300*(1<<30)
             and type(row['active']) is list
             and all(type(q['observed_RSS_bytes']) is int and q['observed_RSS_bytes']>=0
                     for q in row['active']),'strict measured resource samples')
        need(type(row['owned_compiler_tree_RSS_bytes']) is int and
             row['owned_compiler_tree_RSS_bytes']==sum(q['observed_RSS_bytes']for q in row['active']),
             'actual compiler-tree aggregate sample')
    need(type(result['sampled_peak_owned_compiler_tree_RSS_bytes']) is int and
         result['sampled_peak_owned_compiler_tree_RSS_bytes']==max(q['owned_compiler_tree_RSS_bytes']for q in samples),
         'observed aggregate RSS high-water sample, not exact physical peak')




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


def validate(directory,candidate=None):
    result_path=Path(candidate) if candidate is not None else directory/'RESULT.json'
    result = strict_json(result_path)
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
    validate_physical_journal(directory, plan, result)
    return {'status': 'CHECKED_COMPLETE_SELECTED_REPLAY_PHYSICAL_FORECAST', 'modules': len(plan['modules']),
            'axioms': axioms, 'result_sha256': sha(result_path)}


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--context', type=Path, default=S / 'BUILD_CONTEXT.json')
    parser.add_argument('--out', type=Path)
    parser.add_argument('--root', action='append', default=[])
    parser.add_argument('--theorem', action='append', default=[])
    parser.add_argument('--memory-gib', type=int, default=48)
    parser.add_argument('--profile-json', type=Path)
    parser.add_argument('--address-ceiling-gib','--aggregate-gib',dest='aggregate_gib', type=int, default=300,
                        help='Per-task virtual-address ceiling; legacy aggregate-gib alias retained, not an aggregate RAM limit')
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
    need(1 <= args.jobs <= min(22,len(cpus)), 'at most22 actual CPU lanes')
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
    need(1 <= args.aggregate_gib <= 300, 'owner-authorized per-task AS ceiling')
    address_ceiling = args.aggregate_gib << 30
    need(512 <= args.host_reserve_gib <= 4096, 'at least512GiB host reserve')
    host_reserve = args.host_reserve_gib << 30
    if address_ceiling > 48 << 30:
        need(available >= 1024**4, 'high-resource run requires genuinely available1TiB RAM')
    need(available >= host_reserve + min(address_ceiling,INITIAL_FORECAST),
         'actual host reserve plus initial physical forecast')
    def module_memory(name):
        amount = exact.get(name)
        if amount is None:
            matches = [(prefix, value) for prefix, value in prefixes.items()
                       if name == prefix or name.startswith(prefix + '.')]
            amount = max(matches, key=lambda pair: len(pair[0]))[1] if matches else args.memory_gib
        need(amount <= args.aggregate_gib, 'individual AS profile fits per-task ceiling')
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
    need(all(not out.is_relative_to(root) and not root.is_relative_to(out) for root in roots),
         'source and output namespaces must be disjoint')
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
            'resource_scheduler': 'PHYSICAL_RSS_FORECAST_V1',
            'per_task_address_space_ceiling_bytes': address_ceiling,
            'maximum_profile_address_limit_bytes': worker_memory, 'host_reserve_bytes': host_reserve,
            'initial_physical_forecast_bytes': INITIAL_FORECAST,
            'completed_peak_safety_factor': [6,5],
            'heavy_exclusive_address_threshold_bytes': HEAVY_THRESHOLD,
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
    active_processes = {}
    active_lock = threading.Lock()
    resource_peak = {'sampled_owned_compiler_tree_RSS_bytes':0}
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
            run = subprocess.Popen(['/usr/bin/time', '-v', '-o', str(receipt / 'rusage'), *command],
                                   cwd=record['root'], env=env, preexec_fn=limits, stdout=so, stderr=se,
                                   start_new_session=True)
            stat=process_info(run.pid)
            with active_lock:
                active_processes[module]={'pid':run.pid,'start_ticks':stat['start_ticks'] if stat else None}
            try:
                run.wait()
            finally:
                with active_lock:
                    active_processes.pop(module,None)
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
    peak_completed=0
    address_limits={name:row['memory_limit_bytes'] for name,row in modules.items()}
    requested_stop=[]
    def request_stop(sig,frame):requested_stop.append(signal.Signals(sig).name)
    for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGUSR1]:signal.signal(sig,request_stop)
    def snapshots(names):
        with active_lock:
            current=dict(active_processes)
        rows=[]
        for name in sorted(names):
            identity=current.get(name)
            rss=owned_tree_rss(identity['pid'],identity['start_ticks']) if identity else 0
            budget=physical_forecast(address_limits[name],peak_completed)
            rows.append({'module':name,'pid':identity['pid'] if identity else None,
                         'start_ticks':identity['start_ticks'] if identity else None,
                         'observed_RSS_bytes':rss,'physical_forecast_bytes':budget,
                         'potential_growth_bytes':max(0,budget-rss)})
        return rows
    def admission(record,names):
        rows=snapshots(names)
        cap=record['memory_limit_bytes']
        forecast=physical_forecast(cap,peak_completed)
        growth=sum(x['potential_growth_bytes'] for x in rows)
        avail=mem_available()
        need_bytes=host_reserve+growth+forecast
        return {'event':'reserve_before_submit','module':record['module'],
                'module_address_limit_bytes':cap,'physical_forecast_bytes':forecast,
                'completed_peak_RSS_bytes':peak_completed,'host_reserve_bytes':host_reserve,
                'MemAvailable_bytes':avail,'active':rows,'active_potential_growth_bytes':growth,
                'required_available_bytes':need_bytes,'running_workers_before':len(names),
                'running_workers_after':len(names)+1,
                'running_address_limits_before_bytes':sum(address_limits[n] for n in names),
                'running_address_limits_after_bytes':sum(address_limits[n] for n in names)+cap,
                'unix':time.time()}
    def append_event(event):
        with (out/'SCHEDULE.jsonl').open('a') as journal:
            journal.write(json.dumps(event,sort_keys=True)+'\n')
    def record_sample(names):
        active=snapshots(names)
        aggregate=sum(x['observed_RSS_bytes'] for x in active)
        resource_peak['sampled_owned_compiler_tree_RSS_bytes']=max(
            resource_peak['sampled_owned_compiler_tree_RSS_bytes'],aggregate)
        amount=sum(p.stat().st_size for p in out.rglob('*') if p.is_file() and not p.is_symlink())
        with (out/'RESOURCE_SAMPLES.jsonl').open('a') as log:
            log.write(json.dumps({'unix':time.time(),'MemAvailable_bytes':mem_available(),
                'owned_compiler_tree_RSS_bytes':aggregate,'owned_regular_disk_bytes':amount,
                'active':active},sort_keys=True)+'\n')
        need(amount<=300*(1<<30),'experiment-owned scratch cap300GiB')
        if mem_available()<host_reserve and names:
            with active_lock:
                identities=dict(active_processes)
            events=[]
            for name in sorted(identities,reverse=True):
                item=identities[name];current=process_info(item['pid'])
                if current and current['start_ticks']==item['start_ticks']:
                    os.killpg(item['pid'],signal.SIGTERM)
                    events.append({'module':name,**item,'signal':'SIGTERM'})
            atomic(out/'RESOURCE_STOP.json',{'status':'OWNED_HOST_RESERVE_STOP_NOT_OOM',
                'MemAvailable_bytes':mem_available(),'host_reserve_bytes':host_reserve,
                'owned_signals':events})
            raise ValueError('actual available RAM fell below host reserve; owned workers stopped')
    def save_stop():
        atomic(out/'STOPPED.json',{'status':'REQUESTED_DRAIN_NOT_ACCEPTANCE',
            'signals':requested_stop,'completed_modules':sorted(completed),
            'pending_modules':sorted(pending),'owned_active_workers':[]})
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running={}
        while pending or running:
            names=set(running.values())
            record_sample(names)
            if requested_stop and not running:
                save_stop();return
            for name,record in list(pending.items()):
                if requested_stop:break
                if len(running)>=args.jobs:break
                if not all(d not in modules or d in completed for d in record['imports']):continue
                names=set(running.values())
                # Never overlap a heavy Final/audit profile with other workers.
                if any(modules[n]['memory_limit_bytes']>=HEAVY_THRESHOLD for n in names):break
                if record['memory_limit_bytes']>=HEAVY_THRESHOLD and names:break
                event=admission(record,names)
                if event['MemAvailable_bytes']<event['required_available_bytes']:break
                append_event(event)
                running[pool.submit(compile_one,record)]=name
                del pending[name]
            need(bool(running),'no source cycle and enough actual physical RAM for next worker')
            done,_=wait(running,timeout=1,return_when=FIRST_COMPLETED)
            for future in done:
                name=running.pop(future);completed[name]=future.result()
                peak_completed=max(peak_completed,completed[name]['peak_rss_bytes'])
                append_event({'event':'release_after_completion','module':name,
                    'module_address_limit_bytes':modules[name]['memory_limit_bytes'],
                    'actual_peak_RSS_bytes':completed[name]['peak_rss_bytes'],
                    'completed_peak_RSS_bytes':peak_completed,
                    'running_workers_after':len(running),
                    'running_address_limits_after_bytes':sum(modules[n]['memory_limit_bytes'] for n in running.values()),
                    'unix':time.time()})
    records = [completed[record['module']] for record in order]
    audit_source = out / 'source/RamanujanPV/SelectedReplayAudit.lean'
    audit_source.parent.mkdir(parents=True)
    audit_source.write_text(''.join('import ' + target + '\n' for target in targets) +
                            ''.join('#print axioms ' + name + '\n' for name in selected))
    final_record = {'module': 'RamanujanPV.SelectedReplayAudit', 'source': str(audit_source),
                 'root': str(out / 'source'), 'source_sha256': sha(audit_source),
                 'memory_limit_bytes': module_memory('RamanujanPV.SelectedReplayAudit')}
    if requested_stop:
        save_stop();return
    address_limits[final_record['module']]=final_record['memory_limit_bytes']
    final_event=admission(final_record,set())
    need(final_event['MemAvailable_bytes']>=final_event['required_available_bytes'],
         'actual physical RAM for separate final audit')
    append_event(final_event)
    with ThreadPoolExecutor(max_workers=1) as final_pool:
        future=final_pool.submit(compile_one,final_record)
        while not future.done():
            record_sample({final_record['module']})
            wait([future],timeout=1,return_when=FIRST_COMPLETED)
        records.append(future.result())
    peak_completed=max(peak_completed,records[-1]['peak_rss_bytes'])
    append_event({'event':'release_after_completion','module':final_record['module'],
        'module_address_limit_bytes':final_record['memory_limit_bytes'],
        'actual_peak_RSS_bytes':records[-1]['peak_rss_bytes'],
        'completed_peak_RSS_bytes':peak_completed,'running_workers_after':0,
        'running_address_limits_after_bytes':0,'unix':time.time()})
    if requested_stop:
        save_stop();return
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
              'physical_native_association_claimed': False,
              'resource_scheduler':'PHYSICAL_RSS_FORECAST_V1',
              'RESOURCE_SAMPLES_sha256':sha(out/'RESOURCE_SAMPLES.jsonl'),
              'sampled_peak_owned_compiler_tree_RSS_bytes':resource_peak['sampled_owned_compiler_tree_RSS_bytes'],
              'resource_measurement':'GNUtime exact child RSS high-water; compiler-tree RSS sampled1s, not exact aggregate peak. Address-space caps are separate from physical forecasts.'}
    candidate=out/'CANDIDATE.json'
    atomic(candidate,result)
    validate(out,candidate)
    os.replace(candidate,out/'RESULT.json')
    print(json.dumps(validate(out), sort_keys=True))


if __name__ == '__main__':
    main()
