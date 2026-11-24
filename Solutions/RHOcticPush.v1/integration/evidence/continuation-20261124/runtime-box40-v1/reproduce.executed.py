#!/usr/bin/env python3
"""Fresh forty-source Box append above a fully validated source-fresh619 basis.

This is kernel proof checking, not source-first PV. No developer application
object bank is accepted as a generic library. Acceptance survives -O and -OO.
"""
from pathlib import Path
import argparse, importlib.util, json, os, re, shutil, subprocess, sys, threading, time

H = Path(__file__).resolve().parent
S = H.parents[1]
R = S.parents[1]
Q_PATH = S/'integration/supplement/audit_corrected.py'
spec = importlib.util.spec_from_file_location('verified_supplement619', Q_PATH)
Q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(Q)
need, sha, read, save = Q.need, Q.sha, Q.read, Q.save
CAPTURE = H/'cold-capture/SOURCE_CLOSURE.json'

def manifest_check(path):
    need(sha(path) == sha(CAPTURE), 'registered source capture identity')
    m = read(path)
    need(m['schema'] == 'RH_BOX_ZERO_FRESH40_CLOSURE_V1', 'source schema')
    need(m['selector_sha256'] == sha(H/'prepare_cold.py'), 'selector identity')
    need(m['foundation_modules'] == 619 and m['scientific_modules'] == 40
         and m['generated_audit_modules'] == 1, 'exact scoped census')
    need(len(m['modules']) == 41 and len(m['owned_modules']) == 40, 'all new sources')
    need(m['roots'] == [x['module'] for x in m['modules']], 'all dependency probes')
    need(len(set(m['roots'])) == 41, 'duplicate compiler module')
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
    root = Path(root).resolve()
    # This recursively checks every compiler/source/object/log/primary receipt,
    # including the preserved original interrupted origins, before reuse.
    result = Q.validate(root)
    primary = Path(result['primary']['root'])
    pr = read(primary/'RESULT.json')
    foundation = Path(pr['foundation']['root'])
    maps = {}
    for run in [foundation/'pi', foundation/'spectral', foundation/'canonical',
                primary, root]:
        for row in read(run/'BUILD.json')['modules']:
            mod = row['module']
            need(mod not in maps, 'foundation namespace collision')
            obj = run/'objects'/(mod.replace('.', '/')+'.olean')
            need(sha(obj) == row['object_sha256'], 'accepted foundation object drift')
            maps[mod] = {'object': obj, 'object_sha256': row['object_sha256']}
    need(len(maps) == 619, 'complete source-fresh619 only')
    return maps, {'root': str(root), 'RESULT_sha256': sha(root/'RESULT.json'),
                  'BUILD_sha256': sha(root/'BUILD.json'),
                  'manifest_sha256': sha(root/'SOURCE_CLOSURE.executed.json')}

def compile_command(ctx, root, mod, memory, threads):
    rel = mod.replace('.', '/')
    return ['/usr/bin/prlimit', '--as='+str(memory), '--', '/usr/bin/time', '-v',
            ctx['compiler'], '--root='+str(root/'source'), '-j'+str(threads),
            '-o', str(root/'objects'/(rel+'.olean')),
            str(root/'source'/(rel+'.lean'))]

def validate(run, candidate=None):
    run = Path(run).resolve()
    rr = read(candidate or run/'RESULT.json')
    need(rr['status'] == 'PASS_FRESH_BOX40_AND_EXACT_ZERO_CONSUMER', 'complete result')
    need(rr['controller_sha256'] == sha(__file__) == sha(run/'reproduce.executed.py'),
         'controller execution identity')
    need(rr['foundation_controller_sha256'] == sha(Q_PATH), 'foundation validator pin')
    m = manifest_check(run/'SOURCE_CLOSURE.executed.json')
    need(rr['manifest_sha256'] == sha(run/'SOURCE_CLOSURE.executed.json'), 'manifest binding')
    maps, basis = foundation_maps(rr['foundation']['root'])
    need(basis == rr['foundation'], 'changed source-fresh foundation')
    need(not (set(maps) & set(m['roots'])), 'new source namespace')
    ctx = Q.P.context()
    execution = Path(rr['execution_root'])
    need(execution.is_absolute(), 'absolute execution identity')
    build = read(run/'BUILD.json')
    need(sha(run/'BUILD.json') == rr['BUILD_sha256'] and build['status'] == 'PASS',
         'complete actual build binding')
    need(len(build['modules']) == len(m['modules']), 'every fresh compiler route')
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
        need(rss is not None and got['peak_RSS_KiB'] == int(rss[1]), 'measured child peak')
        maps[mod] = {'object': obj, 'object_sha256': got['object_sha256']}
    audit = (run/'logs/FinalBoxZeroAudit.stdout').read_text()
    rows = [json.loads(x.split('RH_BOX_ZERO_THEOREM ', 1)[1])
            for x in audit.splitlines() if 'RH_BOX_ZERO_THEOREM {' in x]
    matches = re.findall(r'RH_BOX_ZERO_AUDIT_PASS (\d+)', audit)
    need(len(matches) == 1 and int(matches[0]) == len(rows) > 0, 'complete theorem audit')
    need(len({x['name'] for x in rows}) == len(rows), 'unique compiler theorem identity')
    need(set(m['final_roots']) <= {x['name'] for x in rows}, 'exact original final roots')
    for row in rows:
        need(row['module'] in m['owned_modules'] and set(row['axioms']) <= Q.P.ALLOW,
             'nonstandard proof axiom or foreign theorem')
    need([x['module'] for x in rr['dependency_probes']] == m['roots'], 'all41 import probes')
    generic = [Path(x).resolve() for x in ctx['generic_libraries']]
    generic += [Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
    by_path = {v['object'].resolve(): v['object_sha256'] for v in maps.values()}
    for probe in rr['dependency_probes']:
        cmd = [ctx['compiler'], '--root='+str(execution/'source'), '--deps',
               str(execution/'source'/(probe['module'].replace('.', '/')+'.lean'))]
        need(probe['command'] == cmd and type(probe['returncode']) is int
             and probe['returncode'] == 0, 'actual dependency probe')
        for suffix in ['stdout', 'stderr']:
            need(sha(run/'dependencies'/probe[suffix]) == probe[suffix+'_sha256'], 'probe log')
        for line in (run/'dependencies'/probe['stdout']).read_text().splitlines():
            path = Path(line).resolve()
            if path.is_relative_to(execution):
                path = (run/path.relative_to(execution)).resolve()
            if any(path.is_relative_to(g) for g in generic):
                continue
            need(path in by_path and sha(path) == by_path[path],
                 'foreign or drifted application object:'+str(path))
    need(rr['compiler_sha256'] == ctx['compiler_sha256'], 'pinned compiler')
    need(rr['fresh_scientific_modules'] == 40 and rr['fresh_audit_modules'] == 1
         and rr['total_source_modules'] == 660, 'transparent source census')
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
        print(json.dumps({'status': 'PASS_BOX40_READBACK', 'optimization': sys.flags.optimize,
                          'fresh_scientific_modules': rr['fresh_scientific_modules']}))
        return
    need(a.foundation is not None and a.out is not None, '--foundation and --out required')
    out = a.out.resolve()
    need(not out.exists(), 'fresh experiment-owned output namespace required')
    m = manifest_check(CAPTURE)
    ctx = Q.P.context()
    maps, basis = foundation_maps(a.foundation)
    need(not (set(maps) & set(m['roots'])), 'fresh namespace')
    if a.check:
        print('PASS_BOX40_PREFLIGHT')
        return
    memory, threads = 64*(1 << 30), 2
    available = Q.available()
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
    sampler = threading.Thread(target=Q.monitor, args=(out, stop, stats), daemon=True)
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
            need(Q.disk(out) <= 300*(1 << 30), 'owned scratch disk cap')
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
        need(Q.disk(out) <= 300*(1 << 30), 'final owned disk cap')
        save(out/'BUILD.json', {'status': 'PASS', 'modules': rows})
        rr = {'schema': 'RH_BOX_FRESH40_REPLAY_V1',
              'status': 'PASS_FRESH_BOX40_AND_EXACT_ZERO_CONSUMER',
              'execution_root': str(out), 'foundation': basis,
              'controller_sha256': sha(__file__), 'foundation_controller_sha256': sha(Q_PATH),
              'manifest_sha256': sha(CAPTURE), 'BUILD_sha256': sha(out/'BUILD.json'),
              'compiler_sha256': ctx['compiler_sha256'], 'fresh_scientific_modules': 40,
              'fresh_audit_modules': 1, 'total_source_modules': 660,
              'fresh_compilations': len(rows), 'seconds': time.monotonic()-start,
              'Lean_threads': threads, 'max_parallel_jobs': 1,
              'per_job_memory_cap_bytes': memory, 'resource_admission': admission,
              'peak_individual_child_RSS_KiB': max(x['peak_RSS_KiB'] for x in rows),
              'sampled_peak_process_tree_RSS_bytes': stats['peak_RSS_bytes'],
              'sampled_peak_owned_disk_bytes': stats['peak_disk_bytes'],
              'owned_disk_before_result_bytes': Q.disk(out),
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
              'trust': 'Ordinary Lean kernel proofs. Explicit RH and general Nicolas/BPT '
                       'literature inputs remain; no desired Box target or moment input. '
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
