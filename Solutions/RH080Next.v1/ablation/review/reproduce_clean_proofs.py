#!/usr/bin/env python3
"""Portable source-cold replay of169 common modules and all13 exact locked payloads.

Needs only this pinned repository, Python, Linux resource tools and the pinned
Lean/generic-library context. No model, SDK, original application objects, runtime
mount archive or historical executor is used. This separate proof replay does not
replace the original matched isolated study or reclassify its primary outcomes.
"""
import argparse, concurrent.futures, json, os, re, shutil, signal, subprocess, threading, time
from pathlib import Path
import run_review as common
import run_supplemental as generator
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
ALLOWED={'propext','Classical.choice','Quot.sound'}


def imports(path):
    return [n for line in path.read_text().splitlines() if line.startswith('import ')
            for n in line[7:].split('--',1)[0].split()]


def available():
    return int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines()
                    if l.startswith('MemAvailable:')))*1024


def rss_tree(pid):
    todo=[pid];seen=set();total=0
    while todo:
        p=todo.pop()
        if p in seen:continue
        seen.add(p)
        try:
            total+=sum(int(l.split()[1])*1024 for l in (Path('/proc')/str(p)/'status').read_text().splitlines() if l.startswith('VmRSS:'))
            for task in (Path('/proc')/str(p)/'task').iterdir():
                try:todo.extend(int(v) for v in (task/'children').read_text().split())
                except (FileNotFoundError,ProcessLookupError):pass
        except (FileNotFoundError,ProcessLookupError):pass
    return total


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--workers',type=int,default=4)
    ap.add_argument('--memory-gib',type=int,default=64)
    ap.add_argument('--payloads',type=Path,default=HERE/'supplemental_evidence_v1/locked_payloads')
    ap.add_argument('--scratch-root',required=True,type=Path)
    ap.add_argument('--scratch-stop-gib',type=int,default=290)
    ap.add_argument('--prepare-only',action='store_true')
    args=ap.parse_args();common.need(not args.out.exists(),'Fresh source-cold output required')
    common.need(1<=args.workers<=4 and args.memory_gib in [32,64] and args.workers*args.memory_gib<=256,'Invalid compiler resource policy')
    context=common.load(args.context);compiler=Path(context['compiler'])
    common.need(common.sha(compiler)==context['compiler_sha256'],'Compiler identity differs')
    common.need(subprocess.check_output([str(compiler),'--version'],text=True).strip()==context['compiler_version'],'Compiler version differs')
    generic_paths=context['generic_lean_path'].split(':')
    common.need(len(generic_paths)==len(context['generic_dependencies'])==8,'Exact8 generic dependencies required')
    for raw,dep in zip(generic_paths,context['generic_dependencies']):
        pkg=Path(raw).parents[3]
        common.need(pkg.name==dep['name'],'Generic dependency path order differs')
        common.need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=pkg,text=True).strip()==dep['revision'],'Generic revision differs')
        common.need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=pkg,text=True),'Generic source dirty')
    ancestor=args.out.parent
    while not ancestor.exists():ancestor=ancestor.parent
    mem=available();disk=shutil.disk_usage(ancestor).free
    common.need(mem>=(256+args.workers*args.memory_gib)*2**30,'Host reserve plus compile allowance unavailable')
    common.need(disk>=2**40,'Independent free disk below1TiB')
    common.need(1<=args.scratch_stop_gib<=290,'Invalid campaign scratch reserve')
    scratch_bytes=int(subprocess.check_output(['du','-sB1',str(args.scratch_root)],text=True).split()[0])
    common.need(scratch_bytes<args.scratch_stop_gib*2**30,'Campaign scratch reserve exhausted')
    inventory=common.load(HERE/'COMMON169_SOURCE_INPUTS.json');source_rows=inventory['modules']
    common.need(len(source_rows)==len({r['module'] for r in source_rows})==169,'Exact169 common source identities required')
    names={r['module'] for r in source_rows};args.out.mkdir(parents=True)
    sources=args.out/'common/source';objects=args.out/'common/objects';logs=args.out/'logs'
    for path in [sources,objects,logs]:path.mkdir(parents=True)
    rows=[]
    for row in source_rows:
        origin=REPO/row['source'];common.need(common.sha(origin)==row['sha256'],'Pinned common source differs '+row['module'])
        deps=imports(origin);common.need(deps==row['imports'],'Pinned imports differ')
        common.need(all(n.split('.')[0] in GENERIC or n in names for n in deps),'Unlisted application import')
        target=sources/(row['module'].replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(origin,target)
        rows.append(dict(row,snapshot=str(target),dependencies=[n for n in deps if n.split('.')[0] not in GENERIC]))
    payload_rows=[]
    for directory in sorted(args.payloads.iterdir()):
        if not directory.is_dir():continue
        lock=common.load(directory/'LOCK.json');modules={}
        for entry in lock['files']:
            p=directory/entry['path'];common.need(p.name==entry['path'] and p.is_file() and common.sha(p)==entry['sha256'],'Locked payload differs')
            if p.suffix=='.lean':modules[p.stem]=p
        common.need(bool(modules),'No exact locked Lean module')
        ordered=[];active=set();seen=set()
        def visit(n):
            if n in seen:return
            common.need(n not in active,'Payload import cycle');active.add(n)
            for d in imports(modules[n]):
                if d in modules:visit(d)
                else:common.need(d.split('.')[0] in GENERIC or d in names,'Unknown payload dependency '+d)
            active.remove(n);seen.add(n);ordered.append(n)
        for n in modules:visit(n)
        payload_rows.append(dict(trial=directory.name,lock_sha256=common.sha(directory/'LOCK.json'),modules=ordered,sources={n:dict(path=str(modules[n]),sha256=common.sha(modules[n])) for n in modules},primary_eligible=False))
    common.need(len(payload_rows)==13 and sum(len(r['modules']) for r in payload_rows)==15,'Exact13locks/15Leanmodules required')
    controller_sha=common.sha(Path(__file__));context_sha=common.sha(args.context)
    common.save(args.out/'PLAN.json',dict(status='FROZEN_PORTABLE_COMMON169_PLUS_EXACT_LOCK15_SOURCE_COLD_PLAN',source_rows=rows,payload_rows=payload_rows,
        compiler_sha256=context['compiler_sha256'],compiler_version=context['compiler_version'],generic_dependencies=context['generic_dependencies'],
        generic_lean_path=context['generic_lean_path'],context_sha256=context_sha,controller_sha256=controller_sha,
        workers=args.workers,memory_gib_each=args.memory_gib,admission_MemAvailable_bytes=mem,admission_disk_free_bytes=disk,
        admission_campaign_scratch_bytes=scratch_bytes,scratch_root=str(args.scratch_root.resolve()),scratch_stop_bytes=args.scratch_stop_gib*2**30,
        host_reserve_bytes=256*2**30,original_application_objects_used=False,SDK_or_model_or_original_executor_used=False,
        original_primary_outcomes_unchanged=True,isolated_primary_trial_replay=False))
    (args.out/'reproduce_clean_proofs.executed.py').write_bytes(Path(__file__).read_bytes())
    if args.prepare_only:print('PREPARED_ONLY; no compiler executed');return
    started=time.monotonic();stop=threading.Event();samples=[];children={};child_lock=threading.Lock();resource_failures=[]
    def terminate_owned():
        with child_lock:owned=list(children.values())
        for child in owned:
            if child.poll() is None:
                try:os.killpg(child.pid,signal.SIGTERM)
                except ProcessLookupError:pass
    def interrupted(signum,frame):
        resource_failures.append('owned controller signal '+str(signum));stop.set();terminate_owned()
    signal.signal(signal.SIGTERM,interrupted);signal.signal(signal.SIGINT,interrupted)
    def sample():
        last_disk=-60;usage=scratch_bytes
        while not stop.is_set():
            elapsed=time.monotonic()-started
            if elapsed-last_disk>=60:
                usage=int(subprocess.check_output(['du','-sB1',str(args.scratch_root)],text=True).split()[0]);last_disk=elapsed
            ram_now=available()
            samples.append(dict(seconds=elapsed,RSS_bytes=rss_tree(os.getpid()),MemAvailable_bytes=ram_now,campaign_scratch_bytes=usage))
            if ram_now<256*2**30 or usage>=args.scratch_stop_gib*2**30:
                resource_failures.append('host RAM or campaign scratch reserve');stop.set();terminate_owned()
            stop.wait(.5)
    sampler=threading.Thread(target=sample,daemon=True);sampler.start();records=[]
    def compile_one(module,source,bank,root,label):
        target=bank/(module.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        stdout=logs/(label+'.stdout');stderr=logs/(label+'.stderr');tm=logs/(label+'.time')
        command=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(args.memory_gib*2**30),'--stack='+str(256*2**20),'--',str(compiler),'-j1','--root='+str(root),'-o',str(target),str(source)]
        env=dict(os.environ,LEAN_PATH=str(bank)+':'+str(objects)+':'+context['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1')
        tick=time.monotonic()
        common.need(not stop.is_set(),'Owned resource stop requested')
        with stdout.open('xb') as o,stderr.open('xb') as e:
            with child_lock:
                common.need(not stop.is_set(),'Owned resource stop requested')
                result=subprocess.Popen(command,env=env,stdout=o,stderr=e,cwd=root,start_new_session=True);children[label]=result
            result.wait()
            with child_lock:children.pop(label,None)
        diagnostic=re.search(r'PANIC|sorryAx|(?m:^|:)\s*error(?::|\()',stdout.read_text()+stderr.read_text())
        record=dict(module=module,label=label,command=command,returncode=result.returncode,seconds=time.monotonic()-tick,
                    source_sha256=common.sha(source),stdout_sha256=common.sha(stdout),stderr_sha256=common.sha(stderr),time_sha256=common.sha(tm),
                    object_sha256=common.sha(target) if target.is_file() else None,strict_accepted=result.returncode==0 and target.is_file() and diagnostic is None)
        common.save(args.out/(label+'.COMPILED.json'),record)
        common.need(record['strict_accepted'],'Compile rejected '+label)
        print('PASS',label,flush=True);return record
    try:
        pending={r['module']:r for r in rows};running={};done=set()
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            while pending or running:
                common.need(not stop.is_set(),'Owned resource stop requested')
                for row in list(pending.values()):
                    if len(running)>=args.workers:break
                    if set(row['dependencies'])<=done:
                        common.need(available()>=256*2**30,'Host reserve breached')
                        n=row['module'];running[pool.submit(compile_one,n,Path(row['snapshot']),objects,sources,n.replace('.','_'))]=n;del pending[n]
                common.need(bool(running),'Common source DAG stalled')
                finished,_=concurrent.futures.wait(running,timeout=30,return_when=concurrent.futures.FIRST_COMPLETED)
                for future in finished:
                    n=running.pop(future);records.append(future.result());done.add(n)
                    (args.out/'PROGRESS.json').write_text(json.dumps(dict(common_completed=len(done),common_total=169,active=list(running.values())))+'\n')
        payload_results=[]
        for row in payload_rows:
            common.need(not stop.is_set(),'Owned resource stop requested')
            trial=row['trial'];trialroot=args.out/'trials'/trial/'source';bank=args.out/'trials'/trial/'objects';trialroot.mkdir(parents=True);bank.mkdir()
            exports=[]
            for module in row['modules']:
                source=trialroot/(module+'.lean');shutil.copyfile(row['sources'][module]['path'],source)
                common.need(common.sha(source)==row['sources'][module]['sha256'],'Exact source changed')
                records.append(compile_one(module,source,bank,trialroot,trial+'-'+module))
                name='IndependentAudit_'+module;path=trialroot/(name+'.lean')
                audit=generator.generic_audit(module).replace('/work/submission/EXPORT.'+module+'.json',str(trialroot/('EXPORT.'+module+'.json')))
                path.write_text(audit);records.append(compile_one(name,path,bank,trialroot,trial+'-'+name))
                export=common.load(trialroot/('EXPORT.'+module+'.json'))
                common.need(export['theorems']>0 and not export['problems'],'Missing full-module proof export')
                for declaration in export['declarations']:
                    common.need(declaration['type'] and declaration['kind']!='axiom' and set(declaration['axioms'])<=ALLOWED,'Unverified submitted theorem')
                exports.append(dict(module=module,sha256=common.sha(trialroot/('EXPORT.'+module+'.json')),declarations=len(export['declarations']),theorem_kind_constants=export['theorems']))
            payload_results.append(dict(trial=trial,lock_sha256=row['lock_sha256'],exports=exports,primary_eligible=False))
    finally:
        stop.set();sampler.join();common.save(args.out/'SAMPLED_RESOURCES.json',dict(interval_seconds=.5,scope='Controller plus own descendants; sampled aggregate RSS is not exact peak',samples=samples,resource_failures=resource_failures))
    common.need(not resource_failures,'Resource interruption; partial artifacts preserved')
    common.need(common.sha(Path(__file__))==controller_sha and common.sha(args.context)==context_sha,'Controller/context changed')
    for row in rows:common.need(common.sha(REPO/row['source'])==row['sha256'],'Common source changed during replay')
    max_rss=[]
    for record in records:
        text=(logs/(record['label']+'.time')).read_text();match=re.search(r'Maximum resident set size \(kbytes\): (\d+)',text)
        common.need(match is not None,'Missing actual child peakRSS');max_rss.append(int(match[1])*1024)
    common.save(args.out/'RESULT.json',dict(status='PASS_PORTABLE_COMMON169_PLUS_ALL13_LOCKED15_LEAN_SOURCE_COLD_STD3',
        common_modules=169,locked_trials=13,locked_source_modules=15,compile_commands=len(records),commands=records,rows=payload_results,
        seconds=time.monotonic()-started,max_child_RSS_bytes=max(max_rss),sampled_group_max_RSS_bytes=max(s['RSS_bytes'] for s in samples),
        min_sampled_MemAvailable_bytes=min(s['MemAvailable_bytes'] for s in samples),failed_compilers=0,SIGKILL_compilers=0,
        exact_cgroup_OOM_counters_available=False,original_application_object_fallback=False,external_model_inference_calls=0,
        primary_successes_added=0,original_primary_outcomes_unchanged=True,scope='Separate portable mathematical proof reproduction; original matched isolated outcomes unchanged'))
    print('PASS portable169common+15lockedsource+15audit compiles; zero new primary successes')


if __name__=='__main__':main()
