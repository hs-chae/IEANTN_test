#!/usr/bin/env python3
"""Continue the SAME originally-fresh source run with per-module weighted caps.
This is an additive profiled continuation, never a cold reset.

This never treats arbitrary old application objects as proof evidence. Every
reused object must have its original successful compiler/source/hash receipt in
the same originally fresh run. Partial attempts and interrupted objects remain
preserved. SIGUSR1/SIGTERM/SIGINT drain current modules without launching more.
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


def finite_float(value):
    number = float(value)
    need(math.isfinite(number), "finite JSON number")
    return number

def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, 'duplicate JSON key')
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite JSON")),
        parse_float=finite_float)


def atomic(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    with temporary.open("w") as stream:
        stream.write(json.dumps(value, indent=2, allow_nan=False) + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    temporary.replace(path)


def validate(directory, candidate=False):
    selected_result=directory/('CANDIDATE_RESULT.json' if candidate else 'RESULT.json')
    result=read_json(selected_result);back=read_json(directory/'READBACK.json')
    need(result['status']==('PENDING_FINAL_READBACK' if candidate else 'FRESH_SEGMENT_CHECKER_SOURCE_CLOSURE_PASS'), 'complete same-fresh-run replay status')
    if not candidate:
        need(result['final_candidate_validation']['status']=='CHECKED_COMPLETE_PROFILED_SAME_FRESH_RUN_CONTINUATION' and sha(directory/'CANDIDATE_RESULT.json')==result['final_candidate_validation']['result_sha256'],'all checks precede final receipt publication')
    run_root=Path(back['original_run_root']);plan_path=run_root/'PLAN.json';plan=read_json(plan_path)
    need(result['plan_sha256']==back['original_plan_sha256']==sha(plan_path), 'same original fixed plan')
    need(result['old_application_objects_used']is False and back['old_application_objects_outside_this_fresh_run_used']is False,'no unrelated old objects')
    need(sha(plan['compiler'])==plan['compiler_sha256'] and sha(plan['context'])==plan['context_sha256'],'original compiler/generic context')
    need(result['readback_sha256']==sha(directory/'READBACK.json'),'exact initial accepted-object readback')
    need(sha(directory/'controller.py')==result['controller_sha256']==back['controller_sha256'],'executed controller snapshot')
    names=[entry['module']for entry in plan['modules']];need(len(names)==len(set(names)),'original unique source identities')
    need([row['module']for row in result['records']]==names+['RamanujanPV.SegmentReplayAudit'],'all original modules plus final audit')
    by_name={row['module']:row for row in result['records']};objects=run_root/'lean'
    for index,row in enumerate(result['records']):
        need(type(row['exit_code'])is int and row['exit_code']==0 and row['source_unchanged_during_compile']is True,'every actual source compile accepted')
        need(Path(row['object']).resolve()==(objects/Path(*row['module'].split('.')).with_suffix('.olean')).resolve(),'same original fresh object bank')
        for field in ['source','object','stdout','stderr','rusage']:
            need(sha(row[field])==row[field+'_sha256'],'actual final artifact '+field)
        need(sha(Path(row['stdout']).parent/'source.lean')==row['source_sha256'],'accepted exact compiler snapshot')
        if row.get('observed_process_limits') is not None:
            need(sha(row['observed_process_limits'])==row['observed_process_limits_sha256'],'actual process cap observation')
            limits=re.search(r'^Max address space\s+(\d+)\s+(\d+)\s+bytes',Path(row['observed_process_limits']).read_text(),re.M)
            need(limits is not None and int(limits[1])==int(limits[2])==row['worker_memory_ceiling_bytes'] and row['observed_limit_matches_requested']is True,'observed actual hard/soft process cap')
        if index<len(names):
            planned=plan['modules'][index]
            need(row['source']==planned['source'] and row['source_sha256']==planned['source_sha256'],'original planned mathematical source')
    for payload in plan['payloads']:need(sha(payload['path'])==payload['sha256'],'actual C source payload')
    reused=back['reused_successful_receipts']
    need(len(reused)==back['reused_count']==result['resumed_count'],'exact reused success population')
    for name,identity in reused.items():
        need(name in names and sha(identity['receipt'])==identity['receipt_sha256'],'preserved original successful receipt')
        need(read_json(identity['receipt'])==by_name[name],'exact unchanged original accepted record')
    caps=back['prospective_module_memory_caps'];aggregate=back['aggregate_worker_memory_ceiling_bytes']
    need(aggregate==result['aggregate_worker_memory_ceiling_bytes'] and aggregate<=300<<30,'matched bounded aggregate')
    reserved={};dispatched=set()
    for line in (directory/'SCHEDULE.jsonl').read_text().splitlines():
        event=json.loads(line,object_pairs_hook=unique_pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')),parse_float=finite_float)
        name=event['module'];need(name in by_name and name not in reused,'only originally pending/final modules dispatched')
        amount=by_name[name]['worker_memory_ceiling_bytes']
        need(event['module_memory_limit_bytes']==amount and (name not in caps or amount==caps[name]),'journal/planned/actual process cap agreement')
        need(event['running_caps_before_bytes']==sum(reserved.values()),'actual reserved before sum')
        if event['event']=='reserve_before_submit':
            need(name not in reserved and name not in dispatched,'unique module dispatch')
            need(event['aggregate_ceiling_bytes']==aggregate,'same aggregate policy')
            reserved[name]=amount;dispatched.add(name)
            need(sum(reserved.values())<=aggregate,'every submission within aggregate ceiling')
        else:
            need(event['event']=='release_after_completion' and name in reserved,'release active task only')
            need(reserved.pop(name)==amount,'release exact actual worker cap')
        need(event['running_caps_after_bytes']==sum(reserved.values()),'actual reserved after sum')
    need(not reserved and dispatched==set(by_name)-set(reused),'all and only pending/final modules dispatched and drained')
    text=Path(result['records'][-1]['stdout']).read_text();observed={}
    for name in plan['selected_theorems']:
        lists=re.findall("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",text)
        empty=re.findall("'"+re.escape(name)+r"' does not depend on any axioms",text)
        need(len(lists)+len(empty)==1,'every mandatory theorem actual axiom report')
        axes=[]if empty else[x.strip()for x in lists[0].split(',')if x.strip()]
        need(len(axes)==len(set(axes))and set(axes)<=STANDARD,'standard axioms only')
        observed[name]=axes
    need(observed==result['axioms'],'actual mandatory final theorem audit')
    return {'status':'CHECKED_COMPLETE_PROFILED_SAME_FRESH_RUN_CONTINUATION','modules':len(names),'reused':len(reused),'result_sha256':sha(selected_result)}


def unique_pairs(pairs):
    result={}
    for key,value in pairs:
        need(key not in result,'duplicate JSON key');result[key]=value
    return result


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--run-root', type=Path)
    parser.add_argument('--out', type=Path)
    parser.add_argument('--jobs', type=int, default=6)
    parser.add_argument('--memory-gib', type=int, default=48)
    parser.add_argument('--cpus', default='72,73,74,75,76,77')
    parser.add_argument('--host-reserve-gib', type=int, default=512)
    parser.add_argument('--profile-json', type=Path)
    parser.add_argument('--aggregate-gib', type=int, default=300)
    parser.add_argument('--readback-only', action='store_true')
    parser.add_argument('--check', type=Path)
    args = parser.parse_args()
    if args.check is not None:
        need(args.run_root is None and args.out is None and not args.readback_only, 'check is separate')
        print(json.dumps(validate(args.check.resolve()), sort_keys=True))
        return
    need(args.run_root is not None and args.out is not None, 'run-root and fresh out required')
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
    need(1 <= args.aggregate_gib <= 300, 'aggregate ceiling1..300GiB')
    aggregate = args.aggregate_gib << 30
    profile = read_json(args.profile_json) if args.profile_json else {'exact': {}, 'prefix': {}}
    need(type(profile) is dict and set(profile) <= {'exact', 'prefix'}, 'known resource profile fields')
    exact, prefixes = profile.get('exact', {}), profile.get('prefix', {})
    for mapping in [exact, prefixes]:
        need(type(mapping) is dict, 'resource profile mapping')
        for name, amount in mapping.items():
            need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', name) is not None,
                 'exact module/prefix identity')
            need(type(amount) is int and 1 <= amount <= args.aggregate_gib, 'profile task fits aggregate ceiling')
    def module_memory(name):
        amount = exact.get(name)
        if amount is None:
            matches = [(key, value) for key, value in prefixes.items()
                       if name == key or name.startswith(key + '.')]
            amount = max(matches, key=lambda item: len(item[0]))[1] if matches else args.memory_gib
        need(amount <= args.aggregate_gib, 'individual task fits aggregate ceiling')
        return amount << 30
    available = int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines()
                         if x.startswith('MemAvailable:'))) * 1024
    need(512 <= args.host_reserve_gib <= 4096, 'preserve at least512GiB host reserve')
    reserve = args.host_reserve_gib << 30
    need(available >= reserve + aggregate, 'actual RAM plus preserved host reserve')
    if aggregate > 48 << 30:
        need(available >= 1024**4, 'high-resource authorization requires genuine available1TiB RAM')
    modules = {entry['module']: entry for entry in plan['modules']}
    need(len(modules) == len(plan['modules']), 'distinct original module identities')
    need(plan['old_application_objects_used'] is False, 'originally fresh application run')
    module_caps = {name: module_memory(name) for name in modules}
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
        need(type(record['exit_code']) is int, 'integer actual compiler result')
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
    for obj in sorted(objects.rglob('*.olean')):
        name = '.'.join(obj.relative_to(objects).with_suffix('').parts)
        if name not in completed:
            destination = quarantine / obj.relative_to(objects)
            if not args.readback_only:
                destination.parent.mkdir(parents=True, exist_ok=True)
                obj.rename(destination)
            moved.append({'module': name, 'original': str(obj), 'preserved': str(destination),
                          'sha256': sha(destination if not args.readback_only else obj),
                          'action': 'moved_preserved' if not args.readback_only else 'preview_only'})
    continuation = {'status': 'EXACT_READBACK_CONTINUATION_STARTED', 'original_run_root': str(run_root),
                    'original_plan_sha256': sha(plan_path), 'controller_sha256': sha(__file__),
                    'reused_count': len(completed), 'reused_successful_receipts': receipt_sources,
                    'quarantined_unaccepted_objects': moved,
                    'resource_profile': profile, 'profile_sha256': sha(args.profile_json) if args.profile_json else None,
                    'prospective_module_memory_caps': module_caps, 'max_workers': args.jobs,
                    'aggregate_worker_memory_ceiling_bytes': aggregate, 'host_reserve_bytes': reserve,
                    'host_memavailable_before_bytes': available, 'cpus': sorted(cpus),
                    'same_fixed_sources_parameters_and_math': True,
                    'old_application_objects_outside_this_fresh_run_used': False}
    atomic(out / 'READBACK.json', continuation)
    if args.readback_only:
        print(json.dumps({'status':'READBACK_ONLY_NOT_REPLAYED','reused_count':len(completed),'pending':len(modules)-len(completed)}))
        return
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
    def compile_one(entry):
        worker_memory = module_memory(entry['module'])
        def limits():
            resource.setrlimit(resource.RLIMIT_AS, (worker_memory, worker_memory))
            os.sched_setaffinity(0, cpus)
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
            proc_limits = Path('/proc')/str(child.pid)/'limits'
            observed_limits = proc_limits.read_text() if proc_limits.exists() else None
            observed_limit_ok = True
            if observed_limits is not None:
                observed = re.search(r'^Max address space\s+(\d+)\s+(\d+)\s+bytes', observed_limits, re.M)
                observed_limit_ok = observed is not None and int(observed[1]) == worker_memory and int(observed[2]) == worker_memory
                (leaf/'observed-process-limits').write_text(observed_limits)
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
                  'address_space_panic': any(word in (leaf/'stdout').read_text()+(leaf/'stderr').read_text() for word in ['out of memory','Out of memory','failed to allocate']),
                  'worker_memory_ceiling_bytes': worker_memory,
                  'observed_limit_matches_requested':observed_limit_ok,
                  'observed_process_limits':str(leaf/'observed-process-limits') if observed_limits is not None else None,
                  'observed_process_limits_sha256':sha(leaf/'observed-process-limits') if observed_limits is not None else None}
        for field, path in [('object', obj), ('stdout', leaf / 'stdout'), ('stderr', leaf / 'stderr'),
                            ('rusage', leaf / 'rusage')]:
            record[field] = str(path)
            if path.is_file():
                record[field + '_sha256'] = sha(path)
        atomic(leaf / 'RUN.json', record)
        print(json.dumps({'module': name, 'exit_code': returncode, 'seconds': record['seconds']}, sort_keys=True),
              flush=True)
        need(returncode == 0 and record['source_unchanged_during_compile'] and observed_limit_ok,
             'continued proof failed/source drift; exact failed attempt preserved')
        return record
    pending = {name: entry for name, entry in modules.items() if name not in completed}
    started = time.monotonic()
    schedule = out / 'SCHEDULE.jsonl'
    def journal(event, name, before, after):
        with schedule.open('a') as stream:
            stream.write(json.dumps({'event':event,'module':name,
                'module_memory_limit_bytes':module_memory(name),'running_caps_before_bytes':before,
                'running_caps_after_bytes':after,'aggregate_ceiling_bytes':aggregate},sort_keys=True)+'\n')
            stream.flush()
            os.fsync(stream.fileno())
    failures = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        running = {}
        while pending or running:
            if not stopping.is_set():
                for name, entry in list(pending.items()):
                    if len(running) >= args.jobs:
                        break
                    if all(dep not in modules or dep in completed for dep in entry['imports']):
                        reserved = sum(module_memory(active) for active in running.values())
                        if reserved + module_memory(name) > aggregate:
                            break
                        now_available = int(next(line.split()[1]for line in Path('/proc/meminfo').read_text().splitlines()if line.startswith('MemAvailable:')))*1024
                        if now_available < reserve+reserved+module_memory(name):
                            break
                        journal('reserve_before_submit',name,reserved,reserved+module_memory(name))
                        running[pool.submit(compile_one, entry)] = name
                        del pending[name]
            with lock:
                live = dict(children)
            atomic(out / 'RUN_STATE.json', {'controller_pid':os.getpid(),'updated_unix_seconds':time.time(),
                'completed':len(completed),'pending':len(pending),'running_modules':list(running.values()),
                'observed_child_pids':live,'drain_requested':stopping.is_set(),'drain_signals':reasons,
                'reserved_worker_memory_bytes':sum(module_memory(name)for name in running.values()),
                'aggregate_worker_memory_ceiling_bytes':aggregate})
            if not running:
                need(stopping.is_set() or not pending, 'source dependency/resource scheduler progress')
                break
            done, _ = wait(running, timeout=5, return_when=FIRST_COMPLETED)
            for future in done:
                name = running.pop(future)
                before = sum(module_memory(active)for active in running.values())+module_memory(name)
                journal('release_after_completion',name,before,before-module_memory(name))
                try:
                    completed[name] = future.result()
                except Exception as error:
                    stopping.set();reasons.append('EXACT_WORKER_FAILURE');failures.append(str(error))
    if failures:
        atomic(out/'DRAINED.json',{'status':'FAILED_AND_CLEANLY_DRAINED','completed':len(completed),
            'pending':len(pending),'running':[],'reasons':reasons,'failures':failures})
        raise ValueError('continued source compile failed; exact partial work preserved: '+str(failures))
    if pending:
        atomic(out / 'DRAINED.json', {'status': 'DRAINED_AT_COMPLETED_MODULE_BOUNDARY',
            'completed': len(completed), 'pending': len(pending), 'running': [], 'reasons': reasons})
        return
    records = [completed[entry['module']] for entry in plan['modules']]
    source = out / 'source/RamanujanPV/SegmentReplayAudit.lean'
    source.parent.mkdir(parents=True)
    source.write_text(''.join('import ' + name + '\n' for name in plan['targets']) +
                      ''.join('#print axioms ' + name + '\n' for name in plan['selected_theorems']))
    final_name = 'RamanujanPV.SegmentReplayAudit'
    journal('reserve_before_submit',final_name,0,module_memory(final_name))
    final = compile_one({'module': 'RamanujanPV.SegmentReplayAudit', 'source': str(source),
                         'root': str(out / 'source'), 'source_sha256': sha(source)})
    journal('release_after_completion',final_name,module_memory(final_name),0)
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
              'resumed_count': continuation['reused_count'],
              'readback_sha256':sha(out/'READBACK.json'),'resource_profile':profile,
              'profile_sha256':sha(args.profile_json)if args.profile_json else None,
              'aggregate_worker_memory_ceiling_bytes':aggregate,'host_reserve_bytes':reserve,
              'prospective_module_memory_caps':module_caps,'controller_sha256':sha(__file__),
              'address_space_panics_this_continuation':sum(row.get('address_space_panic',False)for row in records[continuation['reused_count']:]), 'seconds_this_continuation': time.monotonic() - started,
              'actual_peak_worker_rss_bytes': max(row['peak_rss_bytes'] for row in records),
              'aggregate_peak_RAM_not_measured_by_this_receipt': True,
              'oom_events': sum(row['oom_or_sigkill_event'] for row in records),
              'axioms': axioms, 'records': records,
              'physical_native_caller_proved': False, 'full_prefix_to_1490000000000_verified': False}
    atomic(out/'CANDIDATE_RESULT.json',dict(result,status='PENDING_FINAL_READBACK'))
    result['final_candidate_validation']=validate(out,candidate=True)
    atomic(out / 'RESULT.json', result)
    atomic(run_root / 'RESULT.json', result)
    print(json.dumps({'status': result['status'], 'completed': len(modules),
                      'resumed_count': continuation['reused_count'],
              'readback_sha256':sha(out/'READBACK.json'),'resource_profile':profile,
              'profile_sha256':sha(args.profile_json)if args.profile_json else None,
              'aggregate_worker_memory_ceiling_bytes':aggregate,'host_reserve_bytes':reserve,
              'prospective_module_memory_caps':module_caps,'controller_sha256':sha(__file__),
              'address_space_panics_this_continuation':sum(row.get('address_space_panic',False)for row in records[continuation['reused_count']:]), 'result_sha256': sha(run_root / 'RESULT.json')}))


if __name__ == '__main__':
    main()
