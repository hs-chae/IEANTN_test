#!/usr/bin/env python3
"""Fresh five-source grammar append above the validated fresh32 application.

The clean route first invokes high-driver/reproduce_application.py. This script
never accepts developer application objects as generic libraries. Finite checks
are ordinary kernel checks, not native_decide or an external program execution.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys, threading, time

H = Path(__file__).resolve().parent
R = H.parents[3]
BASE = R/'Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/reproduce_application.py'
spec = importlib.util.spec_from_file_location('actual_fresh_application', BASE)
B = importlib.util.module_from_spec(spec)
spec.loader.exec_module(B)
need, sha, read, save = B.need, B.sha, B.read, B.save
MANIFEST = H/'REPRO_SOURCE_CLOSURE.json'
ALLOW = {'propext', 'Classical.choice', 'Quot.sound'}
STATUS = 'PASS_FRESH_COUNTER_C11_GRAMMAR_AND_SOURCE_INDEXED_MAIN'

def parse_json(text):
    def pairs(items):
        result = {}
        for key,value in items:
            need(key not in result, 'duplicate JSON key in audit')
            result[key] = value
        return result
    return json.loads(text,object_pairs_hook=pairs,
        parse_constant=lambda _: (_ for _ in ()).throw(ValueError('nonfinite audit JSON')))

def pathmod(mod, suffix='.lean'):
    return Path(*mod.split('.')).with_suffix(suffix)

def manifest():
    m = read(MANIFEST)
    need(m['schema'] == 'RH_COUNTER_GRAMMAR_FRESH5_V1' and len(m['modules']) == 5,
         'exact five-source grammar closure')
    need(m['base_controller_sha256'] == sha(BASE), 'base validator identity')
    need(m['freeze_sha256'] == sha(H/'SOURCE_FREEZE.json'), 'scientific freeze identity')
    need([x['module'] for x in m['modules']] ==
         ['CounterGrammar', 'CounterRendererSound', 'CounterSourceSyntax',
          'CounterGrammarConsumer', 'CounterSyntaxAudit'], 'exact compiler identities')
    for x in m['modules']:
        need(sha(H/(x['module']+'.lean')) == x['sha256'], 'source drift:'+x['module'])
    return m

def basis(root):
    root = Path(root).resolve()
    rr = B.verify(root)
    plan = B.source_plan()
    need(len(plan['modules']) == 31 and len(rr['build']) == 32, 'complete fresh31 plus audit')
    ctx = rr['context']
    need(sha(ctx['compiler']) == 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
         'exact pinned Lean compiler')
    for dep in ctx['generic_dependencies']:
        need(dep['name'] in {'mathlib','plausible','LeanSearchClient','importGraph',
                             'proofwidgets','aesop','Qq','batteries','Cli'}, 'generic package scope')
        cp = subprocess.run(['git','rev-parse','HEAD'], cwd=dep['path'], text=True, capture_output=True)
        need(cp.returncode == 0 and cp.stdout.strip() == dep['revision'], 'generic source pin')
        need(subprocess.run(['git','diff','--quiet','HEAD','--'], cwd=dep['path']).returncode == 0,
             'generic tracked source drift')
    for want, got in zip(plan['modules'], rr['build']):
        need(want['module'] == got['module'] and sha(root/'source'/pathmod(want['module'])) ==
             want['sha256'] == got['source_sha256'], 'exact foundation source association')
    for x in plan['resources']:
        need(sha(root/'source'/x['relative']) == x['sha256'], 'actual embedded C resource')
    maps = {}
    for x in rr['build']:
        mod = x['module']
        need(mod not in maps, 'basis module duplicate')
        obj = root/'objects'/pathmod(mod,'.olean')
        need(obj.is_file() and not obj.is_symlink() and sha(obj) == x['object_sha256'],
             'fresh foundation object identity')
        maps[mod] = {'object': obj, 'sha256': x['object_sha256']}
    expected_imports = {x['module']:[d for d in x['imports'] if d in maps]
                        for x in plan['modules']}
    expected_imports['HighApplicationAudit'] = ['HighDriverContract']
    for probe in rr['dependencies']:
        lines = (root/'dependencies'/(probe['module']+'.stdout')).read_text().splitlines()
        resolved = {Path(x).resolve() for x in lines}
        direct = {maps[d]['object'].resolve() for d in expected_imports[probe['module']]}
        need(direct <= resolved, 'foundation omitted declared application import')
        for path in resolved:
            for mod,x in maps.items():
                if path.as_posix().endswith('/'+pathmod(mod,'.olean').as_posix()):
                    need(path == x['object'].resolve(), 'foundation application masqueradesgeneric')
    return maps, ctx, {'root':str(root),'RESULT_sha256':sha(root/'RESULT.json'),
                      'controller_sha256':sha(BASE)}

def command(ctx, root, mod):
    return ['/usr/bin/prlimit','--as='+str(64 << 30),'--','/usr/bin/time','-v',
            '-o',str(root/'logs'/(mod+'.resources')),ctx['compiler'],
            '--root='+str(root/'source'),'-j2','-o',str(root/'objects'/pathmod(mod,'.olean')),
            str(root/'source'/pathmod(mod))]

def disk(root):
    return sum(x.stat().st_size for x in root.rglob('*') if x.is_file() and not x.is_symlink())

def process_rss(pid):
    pending, seen, total = [pid], set(), 0
    while pending:
        p = pending.pop()
        if p in seen:
            continue
        seen.add(p)
        try:
            text = Path('/proc',str(p),'status').read_text()
            match = re.search(r'^VmRSS:\s+(\d+) kB',text,re.M)
            total += int(match[1])*1024 if match else 0
            pending.extend(int(x) for x in Path('/proc',str(p),'task',str(p),'children').read_text().split())
        except (FileNotFoundError,ProcessLookupError):
            pass
    return total

def monitor(out, stop, state):
    start = time.monotonic()
    try:
        with (out/'RESOURCE_SAMPLES.csv').open('w') as f:
            f.write('seconds,tree_RSS_bytes,owned_disk_bytes\n')
            while not stop.is_set():
                rss, used = process_rss(os.getpid()), disk(out)
                state['rss'] = max(state['rss'],rss)
                state['disk'] = max(state['disk'],used)
                state['samples'] += 1
                f.write(f'{time.monotonic()-start:.6f},{rss},{used}\n')
                f.flush()
                stop.wait(.5)
    except BaseException as e:
        state['error'] = repr(e)

def validate(run, candidate=None):
    run = Path(run).resolve()
    rr = read(candidate or run/'RESULT.json')
    need(rr['status'] == STATUS and rr['schema'] == 'RH_COUNTER_GRAMMAR_REPLAY_V1',
         'complete grammar result schema')
    need(rr['controller_sha256'] == sha(__file__) == sha(run/'reproduce.executed.py'),
         'executed controller identity')
    m = manifest()
    need(rr['manifest_sha256'] == sha(MANIFEST) == sha(run/'SOURCE_CLOSURE.executed.json'),
         'exact source selection')
    maps, ctx, base = basis(rr['foundation']['root'])
    need(base == rr['foundation'], 'validated foundation identity')
    execution = Path(rr['execution_root'])
    need(execution.is_absolute(), 'absolute recorded execution root')
    need(len(rr['build']) == 5 and len(rr['dependency_probes']) == 5, 'every compiler/probe route')
    for want, got in zip(m['modules'],rr['build']):
        mod = want['module']
        need(got['module'] == mod and type(got['returncode']) is int and got['returncode'] == 0,
             'actual compiler success')
        source, obj = run/'source'/pathmod(mod), run/'objects'/pathmod(mod,'.olean')
        need(source.is_file() and obj.is_file() and not source.is_symlink() and not obj.is_symlink(),
             'fresh owned source/object')
        need(sha(source) == want['sha256'] == got['source_sha256'] and
             sha(obj) == got['object_sha256'], 'source/object hash association')
        need(got['command'] == command(ctx,execution,mod), 'exact compile invocation')
        for suffix in ['stdout','stderr','resources']:
            need(sha(run/'logs'/(mod+'.'+suffix)) == got[suffix+'_sha256'], 'compiler evidence')
        match = re.search(r'Maximum resident set size \(kbytes\): (\d+)',
                          (run/'logs'/(mod+'.resources')).read_text())
        need(match is not None and type(got['peak_RSS_KiB']) is int and
             int(match[1]) == got['peak_RSS_KiB'] > 0, 'measured child peak RAM')
        maps[mod] = {'object':obj,'sha256':got['object_sha256']}
    audit = (run/'logs/CounterSyntaxAudit.stdout').read_text()
    rows = [parse_json(x.split('COUNTER_GRAMMAR_THEOREM ',1)[1]) for x in audit.splitlines()
            if 'COUNTER_GRAMMAR_THEOREM {' in x]
    counts = re.findall(r'COUNTER_GRAMMAR_AUDIT_PASS (\d+)',audit)
    need(len(counts) == 1 and int(counts[0]) == len(rows) > 0, 'complete actual theorem audit')
    need(len({x['name'] for x in rows}) == len(rows) and {x['name'] for x in rows} ==
         set(m['compiler_theorem_names']), 'exact compiler theorem identities')
    need({x['name'] for x in m['theorems']} <= {x['name'] for x in rows},
         'every current written theorem covered by compiler census')
    for row in rows:
        need(row['module'] in m['owned_modules'] and set(row['axioms']) <= ALLOW,
             'nonstandard or native numerical proof axiom')
    paths = [parse_json(x.split('COUNTER_GRAMMAR_VALUE_PATH ',1)[1]) for x in audit.splitlines()
             if 'COUNTER_GRAMMAR_VALUE_PATH {' in x]
    need(len(paths) == 1 and paths[0]['root'] ==
         'RHOcticPush.CounterSyntax.complete_canonical_source_run' and
         paths[0]['required'] == m['value_path_required'] and
         type(paths[0]['required_count']) is int and paths[0]['required_count'] == 11 and
         type(paths[0]['reached_application_and_boundary_constants']) is int and
         paths[0]['reached_application_and_boundary_constants'] >= 11 and
         type(paths[0]['checked_value_edges']) is int and paths[0]['checked_value_edges'] == 19,
         'final source-run consumes both actual sources and general grammar soundness')
    generic = [Path(x).resolve() for x in ctx['generic_libraries']]
    generic.append(Path(ctx['compiler']).resolve().parents[1]/'lib/lean')
    allowed = {x['object'].resolve():x['sha256'] for x in maps.values()}
    for want, probe in zip(m['modules'],rr['dependency_probes']):
        mod = want['module']
        need(probe['module'] == mod and type(probe['returncode']) is int and probe['returncode'] == 0,
             'actual dependency probe success')
        need(probe['command'] == [ctx['compiler'],'--root='+str(execution/'source'),'--deps',
             str(execution/'source'/pathmod(mod))], 'exact actual import probe')
        for suffix in ['stdout','stderr']:
            need(sha(run/'dependencies'/(mod+'.'+suffix)) == probe[suffix+'_sha256'], 'probe receipt')
        lines = (run/'dependencies'/(mod+'.stdout')).read_text().splitlines()
        need(bool(lines), 'nonempty dependency closure')
        resolved = set()
        for line in lines:
            p = Path(line)
            if p.is_relative_to(execution):
                p = run/p.relative_to(execution)
            p = p.resolve()
            resolved.add(p)
            for application_mod,x in maps.items():
                if p.as_posix().endswith('/'+pathmod(application_mod,'.olean').as_posix()):
                    need(p == x['object'].resolve(), 'application object masquerades as generic')
            if any(p.is_relative_to(g) for g in generic):
                continue
            need(p in allowed and sha(p) == allowed[p], 'foreign/drifted application object:'+str(p))
        direct = {maps[dep]['object'].resolve() for dep in want['application_imports']}
        need(direct <= resolved, 'omitted declared application import:'+want['module'])
    integers = ['fresh_scientific_sources','fresh_audit_sources','foundation_sources',
                'total_scoped_sources','peak_individual_child_RSS_KiB',
                'sampled_peak_tree_RSS_bytes','sampled_peak_owned_disk_bytes']
    need(all(type(rr[x]) is int for x in integers), 'strict integer result metadata')
    admission = rr['resource_admission']
    need(all(type(v) is int for v in admission.values()), 'strict integer resource admission')
    need(admission['host_reserve_bytes'] == 512*(1 << 30) and
         admission['job_memory_cap_bytes'] == 64*(1 << 30) and admission['max_parallel_jobs'] == 1 and
         admission['scratch_cap_bytes'] == 300*(1 << 30) and
         admission['MemAvailable_bytes'] >= 576*(1 << 30) and admission['free_disk_bytes'] >= (1 << 30),
         'exact resource admission policy')
    need(rr['peak_individual_child_RSS_KiB'] == max(x['peak_RSS_KiB'] for x in rr['build']),
         'actual individual high-water mark')
    need(rr['fresh_scientific_sources'] == 4 and rr['fresh_audit_sources'] == 1 and
         rr['foundation_sources'] == 32 and rr['total_scoped_sources'] == 37, 'transparent census')
    need(rr['native_execution_axioms'] is False and rr['full_ISO_C_adequacy_claim'] is False and
         rr['complete_source_first_PV_claim'] is False and rr['exact_count_proved'] is False,
         'honest proof and execution trust boundaries')
    need(type(rr['observed_owned_OOM_events']) is int and rr['observed_owned_OOM_events'] == 0,
         'owned process completion evidence')
    need(sha(run/'RESOURCE_SAMPLES.csv') == rr['resource_samples_sha256'], 'actual resource sampling')
    sample_lines = (run/'RESOURCE_SAMPLES.csv').read_text().splitlines()
    need(sample_lines and sample_lines[0] == 'seconds,tree_RSS_bytes,owned_disk_bytes',
         'exact resource sample schema')
    samples = [x.split(',') for x in sample_lines[1:]]
    need(samples and all(len(x) == 3 for x in samples), 'resource sample schema')
    need(max(int(x[1]) for x in samples) == rr['sampled_peak_tree_RSS_bytes'] and
         max(int(x[2]) for x in samples) == rr['sampled_peak_owned_disk_bytes'] <= 300*(1 << 30),
         'actual measured RAM/disk')
    return rr

def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--foundation',type=Path)
    p.add_argument('--out',type=Path)
    p.add_argument('--verify',type=Path)
    p.add_argument('--check',action='store_true')
    a = p.parse_args()
    if a.verify:
        need(a.foundation is None and a.out is None and not a.check, 'exclusive verify')
        rr = validate(a.verify)
        print(json.dumps({'status':'PASS_COUNTER_GRAMMAR_READBACK','optimization':sys.flags.optimize,
                          'fresh_scientific_sources':rr['fresh_scientific_sources']}))
        return
    need(a.foundation is not None and a.out is not None, '--foundation and --out required')
    out = a.out.resolve()
    need(not out.exists(), 'fresh owned output directory required')
    m = manifest()
    maps,ctx,base = basis(a.foundation)
    if a.check:
        print('PASS_COUNTER_GRAMMAR_PREFLIGHT')
        return
    available = next(int(x.split()[1])*1024 for x in Path('/proc/meminfo').read_text().splitlines()
                     if x.startswith('MemAvailable:'))
    need(available >= 576*(1 << 30), '512GiB host reserve plus64GiB per-job address limit')
    need(out.parent.is_dir() and shutil.disk_usage(out.parent).free >= (1 << 30),
         'separate disk capacity admission')
    out.mkdir()
    for d in ['source','objects','union','logs','dependencies']:
        (out/d).mkdir()
    for mod,x in maps.items():
        link = out/'union'/pathmod(mod,'.olean')
        link.parent.mkdir(parents=True,exist_ok=True)
        link.symlink_to(x['object'])
    for x in m['modules']:
        (out/'source'/pathmod(x['module'])).write_bytes((H/(x['module']+'.lean')).read_bytes())
    (out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    (out/'SOURCE_CLOSURE.executed.json').write_bytes(MANIFEST.read_bytes())
    env = os.environ.copy()
    env['LEAN_PATH'] = ':'.join([str(out/'union'),*ctx['generic_libraries']])
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    start,stop,state = time.monotonic(),threading.Event(),{'rss':0,'disk':0,'samples':0}
    sampler = threading.Thread(target=monitor,args=(out,stop,state),daemon=True)
    sampler.start()
    rows,probes = [],[]
    try:
        for x in m['modules']:
            mod = x['module']
            need(set(x['application_imports']) <= set(maps), 'ordered complete source DAG')
            cmd = command(ctx,out,mod)
            t = time.monotonic()
            with (out/'logs'/(mod+'.stdout')).open('w') as so, \
                 (out/'logs'/(mod+'.stderr')).open('w') as se:
                cp = subprocess.run(cmd,cwd=out/'source',env=env,stdout=so,stderr=se)
            row = {'module':mod,'command':cmd,'returncode':cp.returncode,'seconds':time.monotonic()-t,
                   'source_sha256':sha(out/'source'/pathmod(mod))}
            rows.append(row)
            save(out/'BUILD.json',{'status':'RUNNING','modules':rows})
            need(cp.returncode == 0, 'actual compiler failure:'+mod)
            obj = out/'objects'/pathmod(mod,'.olean')
            row['object_sha256'] = sha(obj)
            for suffix in ['stdout','stderr','resources']:
                row[suffix+'_sha256'] = sha(out/'logs'/(mod+'.'+suffix))
            match = re.search(r'Maximum resident set size \(kbytes\): (\d+)',
                              (out/'logs'/(mod+'.resources')).read_text())
            need(match is not None, 'child resource high-water receipt')
            row['peak_RSS_KiB'] = int(match[1])
            maps[mod] = {'object':obj,'sha256':row['object_sha256']}
            (out/'union'/pathmod(mod,'.olean')).symlink_to(obj)
            need(disk(out) <= 300*(1 << 30) and 'error' not in state, 'owned resources')
            print(len(rows),5,mod,round(row['seconds'],3),flush=True)
        for x in m['modules']:
            mod = x['module']
            cmd = [ctx['compiler'],'--root='+str(out/'source'),'--deps',str(out/'source'/pathmod(mod))]
            cp = subprocess.run(cmd,cwd=out/'source',env=env,capture_output=True,text=True)
            need(cp.returncode == 0, 'actual dependency probe')
            row = {'module':mod,'command':cmd,'returncode':cp.returncode}
            for suffix,text in [('stdout',cp.stdout),('stderr',cp.stderr)]:
                path = out/'dependencies'/(mod+'.'+suffix)
                path.write_text(text)
                row[suffix+'_sha256'] = sha(path)
            probes.append(row)
        stop.set()
        sampler.join()
        need('error' not in state and state['samples'] > 0, 'successful monitoring')
        save(out/'BUILD.json',{'status':'PASS','modules':rows})
        rr = {'schema':'RH_COUNTER_GRAMMAR_REPLAY_V1','status':STATUS,'execution_root':str(out),'foundation':base,
              'controller_sha256':sha(__file__),'manifest_sha256':sha(MANIFEST),
              'build':rows,'dependency_probes':probes,'seconds':time.monotonic()-start,
              'resource_admission':{'MemAvailable_bytes':available,'host_reserve_bytes':512 << 30,
                                    'job_memory_cap_bytes':64 << 30,'max_parallel_jobs':1,
                                    'free_disk_bytes':shutil.disk_usage(out.parent).free,
                                    'scratch_cap_bytes':300 << 30},
              'peak_individual_child_RSS_KiB':max(x['peak_RSS_KiB'] for x in rows),
              'sampled_peak_tree_RSS_bytes':state['rss'],'sampled_peak_owned_disk_bytes':state['disk'],
              'resource_samples_sha256':sha(out/'RESOURCE_SAMPLES.csv'),
              'fresh_scientific_sources':4,'fresh_audit_sources':1,'foundation_sources':32,
              'total_scoped_sources':37,'observed_owned_OOM_events':0,
              'OOM_scope':'All owned compiler/probe processes returned0; no inference from global counters.',
              'measurement':'time-v child high-water RSS,0.5s sampled descendant RSS and regular owned bytes; not exact aggregate/disk high-water marks.',
              'native_execution_axioms':False,'full_ISO_C_adequacy_claim':False,
              'complete_source_first_PV_claim':False,'exact_count_proved':False,
              'trust':'Independent bounded syntax plus preserved formal execution model; external compiler/header/ABI/runtime/stdio/OS/hardware applicability remains explicit.',
              'optimization':sys.flags.optimize}
        save(out/'CANDIDATE.json',rr)
        validate(out,out/'CANDIDATE.json')
        os.replace(out/'CANDIDATE.json',out/'RESULT.json')
        print(STATUS,flush=True)
    except BaseException as error:
        stop.set()
        sampler.join()
        save(out/'FAILURE.json',{'error':repr(error),'completed_modules':len(rows),
                                'seconds':time.monotonic()-start})
        raise

if __name__ == '__main__':
    main()
