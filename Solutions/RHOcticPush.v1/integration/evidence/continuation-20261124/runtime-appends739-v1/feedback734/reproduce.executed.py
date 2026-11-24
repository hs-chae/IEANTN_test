#!/usr/bin/env python3
"""Fresh11 source append connecting full prime-square feedback above723.

This is kernel proof checking, not source-first PV. No developer application
object bank is accepted as a generic library. Acceptance survives -O and -OO.
"""
from pathlib import Path
import argparse, importlib.util, json, math, os, re, shutil, subprocess, sys, threading, time

H = Path(__file__).resolve().parent
S = H.parents[1]
R = S.parents[1]
Q_PATH = H.parent/'ram606/reproduce.py'
spec = importlib.util.spec_from_file_location('verified_supplement619', Q_PATH)
Q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(Q)
need, sha, read, save = Q.need, Q.sha, Q.read, Q.save
Z = Q.Z
CAPTURE = H/'capture/SOURCE_CLOSURE.json'

def strict_payload(text):
    def pairs(rows):
        out={}
        for k,v in rows:
            need(k not in out,'duplicate JSON audit key');out[k]=v
        return out
    def finite(text):
        value=float(text);need(math.isfinite(value),'nonfinite audit float');return value
    return json.loads(text,object_pairs_hook=pairs,parse_float=finite,
                      parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite audit JSON')))

def finite_seconds(value,label):
    need(type(value) in [int,float] and math.isfinite(value) and value>=0,label)

def gnu_seconds(text):
    match=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)',text)
    need(match is not None,'GNU wall time')
    fields=match[1].split(':');need(len(fields) in [2,3],'GNU elapsed format')
    result=0.0
    for field in fields:result=60*result+float(field)
    finite_seconds(result,'finite actual GNU time');return result

def policy_and_resources(run,rr,build):
    need(rr['schema']=='RH_FEEDBACK11_REPLAY_V1','exact replay schema')
    for key,value in [('Lean_threads',2),('max_parallel_jobs',1),
                      ('per_job_memory_cap_bytes',64*(1<<30)),('fresh_compilations',11)]:
        need(type(rr[key]) is int and rr[key]==value,'exact resource policy:'+key)
    admission=read(run/'RESOURCE_ADMISSION.json')
    need(rr['resource_admission']==admission,'actual admission-file binding')
    need(set(admission)=={'MemAvailable_bytes','host_reserve_bytes','per_job_address_space_cap_bytes',
         'max_parallel_jobs','free_disk_bytes','scratch_cap_bytes'},'admission schema')
    need(all(type(v) is int for v in admission.values()),'integer admission')
    need(admission['host_reserve_bytes']==512*(1<<30)
         and admission['per_job_address_space_cap_bytes']==64*(1<<30)
         and admission['max_parallel_jobs']==1 and admission['scratch_cap_bytes']==300*(1<<30)
         and admission['MemAvailable_bytes']>=admission['host_reserve_bytes']+admission['per_job_address_space_cap_bytes']
         and admission['free_disk_bytes']>=10*(1<<30),'admitted resource policy')
    finite_seconds(rr['seconds'],'finite observed build/probe wall time')
    total_gnu=0.0;total_measured=0.0
    for row in build['modules']:
        finite_seconds(row['seconds'],'finite compiler duration')
        actual=gnu_seconds((run/'logs'/(row['module']+'.stderr')).read_text())
        need(actual<=row['seconds']+1 and row['seconds']<=actual+5,'compiler duration against actual GNU time')
        total_gnu+=actual;total_measured+=row['seconds']
    need(total_measured<=rr['seconds']+1 and total_gnu<=rr['seconds']+11,'actual phase duration')
    need(type(rr['owned_disk_before_result_bytes']) is int
         and rr['sampled_peak_owned_disk_bytes']<=rr['owned_disk_before_result_bytes']<=300*(1<<30)
         and Z.Q.disk(run)<=300*(1<<30),'actual owned final disk cap')
    receipt_bytes=sum((run/name).stat().st_size for name in ['RESULT.json','CANDIDATE.json'] if (run/name).is_file())
    need(Z.Q.disk(run)-receipt_bytes==rr['owned_disk_before_result_bytes'],
         'exact owned disk before result, normalized only for final receipt files')

def manifest_check(path):
    need(sha(path) == sha(CAPTURE), 'registered source capture identity')
    m = read(path)
    need(m['schema'] == 'RH_FEEDBACK11_SOURCE_CLOSURE_V1', 'source schema')
    need(m['selector_sha256'] == sha(H/'prepare.py'), 'selector identity')
    need(m['foundation_modules'] == 723 and m['new_modules'] == 11
         and m['all_source_count'] == 734, 'exact scoped census')
    need(len(m['modules']) == 11 and len(m['owned_modules']) == 9, 'all new sources')
    need(m['roots'] == [x['module'] for x in m['modules']], 'all dependency probes')
    need(len(m['final_roots']) == 83 and len(set(m['final_roots'])) == 83,
         'complete canonical inventory')
    need(m['body_roots'] == m['final_roots'] +
         ['RHOcticPush.Network.fully_derived_box_network',
          'RHOcticPush.Network.fully_derived_spectral_box_network',
          'RHOcticPush.Network.fully_derived_spectral_ramanujan',
          'RHOcticPush.Network.fully_derived_feedback_box_network'] +
         m['comparison_roots'], 'complete body roots')
    need(m['comparison_roots'] == ['RHOcticPush.ZeroComparison.positive_inverse_band',
         'RHOcticPush.ZeroComparison.actual_both_sign_inverse_lower',
         'RHOcticPush.ZeroComparison.excludes_both_sign_sixteen'], 'exact comparison roots')
    for q in m['canonical_metadata']:
        need(sha(R/q['path']) == q['sha256'], 'canonical metadata identity')
    q = m['exact_type_inventory']
    need(sha(R/q['path']) == q['sha256'] and len(read(R/q['path'])['claims']) == 11,
         'all11 verbatim generated theorem types')
    need(len(set(m['roots'])) == 11, 'duplicate compiler module')
    for f in m['freezes']:
        need(sha(R/f['path']) == f['sha256'], 'scientific freeze drift')
    done = set()
    for row in m['modules']:
        need(sha(R/row['path']) == row['sha256'], 'captured source drift:'+row['module'])
        if row['original_path'] is not None:
            need(sha(R/row['original_path']) == row['sha256'],
                 'current scientific source drift:'+row['module'])
        need(set(row['application_imports']) & set(m['roots']) <= done,
             'incomplete ordered fresh DAG')
        done.add(row['module'])
    return m

def foundation_maps(root):
    root=Path(root).resolve()
    result=Q.validate(root)
    maps,old=Q.foundation_maps(Path(result['foundation']['root']))
    need(len(maps)==712,'verified712 prefix of accepted723')
    for row in read(root/'BUILD.json')['modules']:
        mod=row['module'];obj=root/'objects'/(mod.replace('.','/')+'.olean')
        need(mod not in maps and sha(obj)==row['object_sha256'],'validated723 exact object identity')
        maps[mod]={'object':obj,'object_sha256':row['object_sha256']}
    need(len(maps)==723,'complete recursively validated723')
    need(len(result['dependency_probes'])==11,'all11 prior new probes')
    # Q.validate rechecks the complete723 chain and all347 earlier recorded
    # direct-import probes. Its eleven additional probes give358 recorded roots;
    # canonical24 did not record --deps and is not retroactively relabelled.
    prior_payloads=0
    log_roots=set()
    for row in maps.values():
        obj=str(row['object'])
        need('/objects/' in obj,'owned basis object route')
        log_roots.add(Path(obj.split('/objects/',1)[0])/'logs')
    for directory in log_roots:
        for stdout in directory.glob('*.stdout'):
            for line in stdout.read_text().splitlines():
                hit=re.search(r'RH_[A-Z_]*(?:THEOREM|BODY) (\{.*)$',line)
                if hit:
                    strict_payload(hit[1]);prior_payloads+=1
    need(prior_payloads>0,'nonempty strict prior audit payload scope')
    return maps,{'root':str(root),'RESULT_sha256':sha(root/'RESULT.json'),
                 'BUILD_sha256':sha(root/'BUILD.json'),
                 'manifest_sha256':sha(root/'SOURCE_CLOSURE.executed.json'),
                 'prior_direct_import_probe_count':old['prior_direct_import_probe_count']+11,
                 'strict_prior_audit_payload_lines':prior_payloads}

def compile_command(ctx, root, mod, memory, threads):
    rel = mod.replace('.', '/')
    return ['/usr/bin/prlimit', '--as='+str(memory), '--', '/usr/bin/time', '-v',
            ctx['compiler'], '--root='+str(root/'source'), '-j'+str(threads),
            '-o', str(root/'objects'/(rel+'.olean')),
            str(root/'source'/(rel+'.lean'))]

def validate(run, candidate=None):
    run = Path(run).resolve()
    rr = read(candidate or run/'RESULT.json')
    need(rr['status'] == 'PASS_FRESH_FEEDBACK11_FULL_FUNCTION_AND_CANONICAL_CONSUMERS', 'complete result')
    need(rr['controller_sha256'] == sha(__file__) == sha(run/'reproduce.executed.py'),
         'controller execution identity')
    need(rr['foundation_controller_sha256'] == sha(Q_PATH), 'foundation validator pin')
    m = manifest_check(run/'SOURCE_CLOSURE.executed.json')
    need(rr['manifest_sha256'] == sha(run/'SOURCE_CLOSURE.executed.json'), 'manifest binding')
    maps, basis = foundation_maps(rr['foundation']['root'])
    need(basis == rr['foundation'], 'changed source-fresh foundation')
    need(not (set(maps) & set(m['roots'])), 'new source namespace')
    ctx = Z.Q.P.context()
    execution = Path(rr['execution_root'])
    need(execution.is_absolute(), 'absolute execution identity')
    build = read(run/'BUILD.json')
    need(sha(run/'BUILD.json') == rr['BUILD_sha256'] and build['status'] == 'PASS',
         'complete actual build binding')
    need(len(build['modules']) == len(m['modules']), 'every fresh compiler route')
    policy_and_resources(run,rr,build)
    for want, got in zip(m['modules'], build['modules']):
        mod = want['module']
        rel = mod.replace('.', '/')
        source, obj = run/'source'/(rel+'.lean'), run/'objects'/(rel+'.olean')
        need(got['module'] == mod and type(got['returncode']) is int
             and got['returncode'] == 0, 'actual compiler status')
        need(source.is_file() and obj.is_file() and not source.is_symlink()
             and not obj.is_symlink(), 'fresh owned source and object')
        need(sha(source) == want['sha256'] == got['source_sha256']
             and sha(obj) == got['object_sha256'], 'source/object association')
        need(got['command'] == compile_command(ctx, execution, mod,
             rr['per_job_memory_cap_bytes'], rr['Lean_threads']), 'exact compiler command')
        for suffix in ['stdout', 'stderr']:
            need(sha(run/'logs'/(mod+'.'+suffix)) == got[suffix+'_sha256'], 'compiler log')
        rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)',
                        (run/'logs'/(mod+'.stderr')).read_text())
        need(rss is not None and type(got['peak_RSS_KiB']) is int and got['peak_RSS_KiB'] == int(rss[1]), 'measured child peak')
        maps[mod] = {'object': obj, 'object_sha256': got['object_sha256']}
    audit = (run/'logs/FinalFeedbackAudit.stdout').read_text()
    rows = [strict_payload(x.split('RH_FEEDBACK_FINAL_THEOREM ', 1)[1])
            for x in audit.splitlines() if 'RH_FEEDBACK_FINAL_THEOREM {' in x]
    matches = re.findall(r'RH_FEEDBACK_FINAL_AUDIT_PASS (\d+)', audit)
    need(len(matches) == 1 and int(matches[0]) == len(rows) > 0, 'complete theorem audit')
    need(len({x['name'] for x in rows}) == len(rows), 'unique compiler theorem identity')
    need(set(m['new_canonical_roots']) <= {x['name'] for x in rows}, 'all new actual canonical proofs')
    for row in rows:
        need(type(row) is dict and set(row)=={'name','module','axioms'}
             and type(row['name']) is str and type(row['module']) is str
             and type(row['axioms']) is list and all(type(a) is str for a in row['axioms']),
             'exact theorem audit payload schema')
        need(row['module'] in m['owned_modules'] and set(row['axioms']) <= Z.Q.P.ALLOW,
             'nonstandard proof axiom or foreign theorem')
    bodies = [strict_payload(x.split('RH_FEEDBACK_FINAL_BODY ', 1)[1])
              for x in audit.splitlines() if 'RH_FEEDBACK_FINAL_BODY {' in x]
    need([x['theorem'] for x in bodies] == m['body_roots'], 'every exact final theorem body')
    for row in bodies:
        need(type(row) is dict and set(row)=={'theorem','axioms','lambda_parameters'}
             and type(row['theorem']) is str and type(row['axioms']) is list
             and all(type(a) is str for a in row['axioms'])
             and type(row['lambda_parameters']) is list
             and all(type(p) is dict and set(p)=={'name','used_in_body'}
                     and type(p['name']) is str for p in row['lambda_parameters']),
             'exact body audit payload schema')
        need(set(row['axioms']) <= Z.Q.P.ALLOW, 'actual final proof dependency axioms')
        need(all(type(p['used_in_body']) is bool and p['used_in_body'] is True
                 for p in row['lambda_parameters']), 'unused claimed final proof input')
    need([x['module'] for x in rr['dependency_probes']] == m['roots'], 'all11 import probes')
    generic = [Path(x).resolve() for x in ctx['generic_libraries']]
    generic += [Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
    by_path = {v['object'].resolve(): v['object_sha256'] for v in maps.values()}
    wants = {x['module']: x for x in m['modules']}
    for probe in rr['dependency_probes']:
        cmd = [ctx['compiler'], '--root='+str(execution/'source'), '--deps',
               str(execution/'source'/(probe['module'].replace('.', '/')+'.lean'))]
        need(probe['command'] == cmd and type(probe['returncode']) is int
             and probe['returncode'] == 0, 'actual dependency probe')
        for suffix in ['stdout', 'stderr']:
            need(sha(run/'dependencies'/probe[suffix]) == probe[suffix+'_sha256'], 'probe log')
        lines = (run/'dependencies'/probe['stdout']).read_text().splitlines()
        need(bool(lines) and all(bool(x.strip()) for x in lines),
             'nonempty actual new dependency inventory')
        seen = set()
        for line in lines:
            path = Path(line).resolve()
            if path.is_relative_to(execution):
                path = (run/path.relative_to(execution)).resolve()
            seen.add(path)
            generic_roots=[g for g in generic if path.is_relative_to(g)]
            if generic_roots:
                for g in generic_roots:
                    identity='.'.join(path.relative_to(g).with_suffix('').parts)
                    need(identity not in maps and identity not in m['roots'],
                         'application module masquerading as generic:'+identity)
                continue
            need(path in by_path and sha(path) == by_path[path],
                 'foreign or drifted application object:'+str(path))
        expected = {maps[dep]['object'].resolve()
                    for dep in wants[probe['module']]['application_imports']}
        need(expected <= seen, 'declared direct application import missing:'+probe['module'])
    need(rr['compiler_sha256'] == ctx['compiler_sha256'], 'pinned compiler')
    need(all(type(rr[k]) is int for k in ['fresh_scientific_modules',
         'fresh_audit_modules', 'total_source_modules', 'Lean_threads',
         'per_job_memory_cap_bytes', 'peak_individual_child_RSS_KiB',
         'sampled_peak_process_tree_RSS_bytes', 'sampled_peak_owned_disk_bytes']),
         'exact integer resource and census fields')
    need(rr['fresh_scientific_modules'] == 10 and rr['fresh_audit_modules'] == 1
         and rr['total_source_modules'] == 734, 'transparent source census')
    need(rr['DEV_application_objects_used'] is False
         and rr['historical_application_cache_used'] is False
         and rr['source_first_PV_claim'] is False, 'trust categories')
    need(type(rr['observed_process_OOM_events']) is int
         and rr['observed_process_OOM_events'] == 0, 'successful process evidence')
    need(sha(run/'TREE_RSS.csv') == rr['TREE_RSS_sha256'], 'resource evidence')
    sample = (run/'TREE_RSS.csv').read_text().splitlines()
    need(sample[0] == 'seconds,process_tree_RSS_bytes,process_count,owned_disk_bytes'
         and len(sample) > 1, 'actual resource sample schema')
    parsed = [x.split(',') for x in sample[1:]]
    need(all(len(x) == 4 for x in parsed), 'resource rows')
    for row in parsed:
        finite_seconds(float(row[0]),'finite sample time')
        need(all(re.fullmatch(r'[0-9]+',x) is not None for x in row[1:]),'integer sample resources')
        need(int(row[2])>0,'live sampled process count')
    need(max(int(x[1]) for x in parsed) == rr['sampled_peak_process_tree_RSS_bytes'],
         'aggregate peak RAM sample')
    need(max(int(x[3]) for x in parsed) == rr['sampled_peak_owned_disk_bytes']
         <= 300*(1 << 30), 'actual sampled disk and cap')
    need(max(x['peak_RSS_KiB'] for x in build['modules'])
         == rr['peak_individual_child_RSS_KiB'], 'individual high-water mark')
    return rr

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--foundation', type=Path)
    ap.add_argument('--out', type=Path)
    ap.add_argument('--verify', type=Path)
    ap.add_argument('--check', action='store_true')
    a = ap.parse_args()
    if a.verify:
        need(a.foundation is None and a.out is None and not a.check, 'exclusive verify mode')
        rr = validate(a.verify)
        print(json.dumps({'status': 'PASS_FEEDBACK11_READBACK', 'optimization': sys.flags.optimize,
                          'fresh_scientific_modules': rr['fresh_scientific_modules']}))
        return
    need(a.foundation is not None and a.out is not None, '--foundation and --out required')
    out = a.out.resolve()
    need(not out.exists(), 'fresh experiment-owned output namespace required')
    m = manifest_check(CAPTURE)
    ctx = Z.Q.P.context()
    maps, basis = foundation_maps(a.foundation)
    need(not (set(maps) & set(m['roots'])), 'fresh namespace')
    if a.check:
        print('PASS_FEEDBACK11_PREFLIGHT')
        return
    memory, threads = 64*(1 << 30), 2
    available = Z.Q.available()
    reserve = 512*(1 << 30)
    need(available >= reserve+memory, 'preserve512GiB host reserve plus actual job cap')
    need(out.parent.is_dir(), 'owned parent must already exist')
    free = shutil.disk_usage(out.parent).free
    need(free >= 10*(1 << 30), 'separate disk admission')
    out.mkdir()
    admission = {'MemAvailable_bytes': available, 'host_reserve_bytes': reserve,
                 'per_job_address_space_cap_bytes': memory, 'max_parallel_jobs': 1,
                 'free_disk_bytes': free, 'scratch_cap_bytes': 300*(1 << 30)}
    save(out/'RESOURCE_ADMISSION.json', admission)
    for directory in ['source', 'objects', 'union', 'logs', 'dependencies']:
        (out/directory).mkdir()
    (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    (out/'SOURCE_CLOSURE.executed.json').write_bytes(CAPTURE.read_bytes())
    for mod, row in maps.items():
        link = out/'union'/(mod.replace('.', '/')+'.olean')
        link.parent.mkdir(parents=True, exist_ok=True)
        link.symlink_to(row['object'])
    for row in m['modules']:
        path = out/'source'/(row['module'].replace('.', '/')+'.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes((R/row['path']).read_bytes())
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(out/'union'), *ctx['generic_libraries']])
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    start = time.monotonic()
    rows, probes = [], []
    stats = {'peak_RSS_bytes': 0, 'peak_disk_bytes': 0, 'last_disk': 0, 'samples': 0}
    stop = threading.Event()
    sampler = threading.Thread(target=Z.Q.monitor, args=(out, stop, stats), daemon=True)
    sampler.start()
    try:
        for want in m['modules']:
            mod = want['module']
            need(set(want['application_imports']) <= set(maps), 'compile DAG closure')
            obj = out/'objects'/(mod.replace('.', '/')+'.olean')
            obj.parent.mkdir(parents=True, exist_ok=True)
            cmd = compile_command(ctx, out, mod, memory, threads)
            so, se = out/'logs'/(mod+'.stdout'), out/'logs'/(mod+'.stderr')
            t = time.monotonic()
            with so.open('w') as fo, se.open('w') as fe:
                cp = subprocess.run(cmd, cwd=out/'source', env=env, text=True,
                                    stdout=fo, stderr=fe)
            rss = re.search(r'Maximum resident set size \(kbytes\): (\d+)', se.read_text())
            need(rss is not None, 'actual child RAM receipt')
            source = out/'source'/(mod.replace('.', '/')+'.lean')
            row = {'module': mod, 'command': cmd, 'returncode': cp.returncode,
                   'seconds': time.monotonic()-t, 'source_sha256': sha(source),
                   'stdout_sha256': sha(so), 'stderr_sha256': sha(se),
                   'peak_RSS_KiB': int(rss[1])}
            if cp.returncode == 0:
                row['object_sha256'] = sha(obj)
            rows.append(row)
            save(out/'BUILD.json', {'status': 'RUNNING' if cp.returncode == 0 else 'FAIL',
                                   'modules': rows})
            need(cp.returncode == 0, 'compiler failure:'+mod)
            need(row['source_sha256'] == want['sha256'], 'source changed during compile')
            need('monitor_error' not in stats, 'resource monitor failure')
            need(Z.Q.disk(out) <= 300*(1 << 30), 'owned scratch disk cap')
            maps[mod] = {'object': obj, 'object_sha256': row['object_sha256']}
            link = out/'union'/(mod.replace('.', '/')+'.olean')
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(obj)
            print(len(rows), len(m['modules']), mod, round(row['seconds'], 3), flush=True)
        for mod in m['roots']:
            cmd = [ctx['compiler'], '--root='+str(out/'source'), '--deps',
                   str(out/'source'/(mod.replace('.', '/')+'.lean'))]
            cp = subprocess.run(cmd, cwd=out/'source', env=env, capture_output=True, text=True)
            so, se = out/'dependencies'/(mod+'.stdout'), out/'dependencies'/(mod+'.stderr')
            so.write_text(cp.stdout)
            se.write_text(cp.stderr)
            need(cp.returncode == 0, 'dependency probe failure:'+mod)
            probes.append({'module': mod, 'command': cmd, 'returncode': cp.returncode,
                           'stdout': so.name, 'stderr': se.name,
                           'stdout_sha256': sha(so), 'stderr_sha256': sha(se)})
        stop.set()
        sampler.join()
        need('monitor_error' not in stats and stats['samples'] > 0, 'complete sampling')
        need(Z.Q.disk(out) <= 300*(1 << 30), 'final owned disk cap')
        save(out/'BUILD.json', {'status': 'PASS', 'modules': rows})
        rr = {'schema': 'RH_FEEDBACK11_REPLAY_V1',
              'status': 'PASS_FRESH_FEEDBACK11_FULL_FUNCTION_AND_CANONICAL_CONSUMERS',
              'execution_root': str(out), 'foundation': basis,
              'controller_sha256': sha(__file__), 'foundation_controller_sha256': sha(Q_PATH),
              'manifest_sha256': sha(CAPTURE), 'BUILD_sha256': sha(out/'BUILD.json'),
              'compiler_sha256': ctx['compiler_sha256'], 'fresh_scientific_modules': 10,
              'fresh_audit_modules': 1, 'total_source_modules': 734,
              'fresh_compilations': len(rows), 'seconds': time.monotonic()-start,
              'Lean_threads': threads, 'max_parallel_jobs': 1,
              'per_job_memory_cap_bytes': memory, 'resource_admission': admission,
              'peak_individual_child_RSS_KiB': max(x['peak_RSS_KiB'] for x in rows),
              'sampled_peak_process_tree_RSS_bytes': stats['peak_RSS_bytes'],
              'sampled_peak_owned_disk_bytes': stats['peak_disk_bytes'],
              'owned_disk_before_result_bytes': Z.Q.disk(out),
              'TREE_RSS_sha256': sha(out/'TREE_RSS.csv'), 'dependency_probes': probes,
              'observed_process_OOM_events': 0,
              'OOM_evidence': 'All owned compilation and dependency-probe processes returned0; '
                              'no claim about unattributed global host counters.',
              'RAM_measurement': 'time -v per-child high-water mark; controller descendant '
                                 'VmRSS sampled every0.5s, not an exact aggregate high-water mark.',
              'disk_measurement': 'Owned regular-file bytes sampled every5s and checked at '
                                  'compiler completions/final, not an exact intra-compiler peak.',
              'DEV_application_objects_used': False, 'historical_application_cache_used': False,
              'source_first_PV_claim': False,
              'trust': 'Ordinary Lean kernel proofs. Explicit RH and GENERAL published Perron/Nicolas/BPT '
                       'literature inputs remain explicit. The same four providers construct actual J, prime-power '
                       'feedback and the complete ordinary-pi envelope. No new GM/Buthe input or desired '
                       'numerical conclusion is assumed. The entire35-ray, min70 and whole-function gain '
                       'are retained; the .42 scalar result is a convenient corollary, not optimality. '
                       'Pinned Lean compiler/runtime/OS/hardware and generic libraries trusted.',
              'python_optimization': sys.flags.optimize}
        candidate = out/'CANDIDATE.json'
        save(candidate, rr)
        validate(out, candidate)
        os.replace(candidate, out/'RESULT.json')
        print(rr['status'], flush=True)
    except BaseException as error:
        stop.set()
        sampler.join()
        save(out/'FAILURE.json', {'error': repr(error), 'completed_modules': len(rows),
                                 'seconds': time.monotonic()-start})
        raise

if __name__ == '__main__':
    main()
