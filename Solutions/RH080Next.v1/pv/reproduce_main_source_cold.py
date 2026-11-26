#!/usr/bin/env python3
"""Rebuild the pinned entire numerical C program proof universe without app caches.

Reuses the source-associated compiler's strict checks/atomic receipts and the
primal cold controller's dependency scheduler/descendant-RSS approach. Literal
N17/N24 FFT trace data are separate experiments and are not copied or compiled.
"""
from __future__ import annotations
import argparse, concurrent.futures, json, os, re, shutil, signal, subprocess
import threading, time
from pathlib import Path
from compile_verified_batch import GENERIC, atomic, imports, need, sha

HERE=Path(__file__).resolve().parent
ALLOWED_AXIOMS={'propext','Classical.choice','Quot.sound'}
FORBIDDEN=re.compile(r'PANIC|sorryAx|(?m:^|:)\s*error(?::|\()')


def available_ram():
    return int(next(l.split()[1] for l in Path('/proc/meminfo').read_text().splitlines() if l.startswith('MemAvailable:')))*1024


def tree_rss(pid):
    todo=[pid];seen=set();rss=0
    while todo:
        current=todo.pop()
        if current in seen:continue
        seen.add(current)
        try:
            base=Path('/proc')/str(current)
            rss+=sum(int(l.split()[1])*1024 for l in (base/'status').read_text().splitlines() if l.startswith('VmRSS:'))
            for task in (base/'task').iterdir():
                try:todo.extend(map(int,(task/'children').read_text().split()))
                except (FileNotFoundError,ProcessLookupError):pass
        except (FileNotFoundError,ProcessLookupError,PermissionError):pass
    return rss


def directory_bytes(path):
    return int(subprocess.check_output(['du','-sB1',str(path)],text=True).split()[0])


def validate_context(path):
    c=json.loads(path.read_text());compiler=Path(c['compiler'])
    need(sha(compiler)==c['compiler_sha256'],'Compiler bytes differ')
    need(subprocess.check_output([str(compiler),'--version'],text=True).strip()==c['compiler_version'],'Compiler version differs')
    paths=c['generic_lean_path'].split(':');need(len(paths)==len(c['generic_dependencies']),'Generic dependency population differs')
    for path,dep in zip(paths,c['generic_dependencies']):
        package=Path(path).parents[3]
        need(package.name==dep['name'],'Generic path identity/order differs')
        need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=package,text=True).strip()==dep['revision'],'Generic commit differs')
        need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=package,text=True),'Generic tracked source dirty')
    return c


def module_valid(run,row):
    name=row['module'];receipt=run/(name+'.COMPILED.json')
    need(receipt.is_file(),'Missing actual compiler receipt '+name)
    r=json.loads(receipt.read_text());need(r['module']==name and r['exitcode']==0,'Rejected compiler execution '+name)
    source=run/'source'/(name.replace('.','/')+'.lean');obj=run/'objects'/(name.replace('.','/')+'.olean')
    need(source.is_file() and sha(source)==row['source_sha256'],'Frozen source differs '+name)
    need(Path(row['origin']).is_file() and sha(Path(row['origin']))==row['source_sha256'],'Pinned source changed '+name)
    need(obj.is_file() and sha(obj)==r['object_sha256'],'Missing/changed actual proof object '+name)
    out=run/'logs'/(name+'.stdout');err=run/'logs'/(name+'.stderr');tm=run/'logs'/(name+'.time')
    for file,key in [(out,'stdout_sha256'),(err,'stderr_sha256'),(tm,'time_sha256')]:
        need(file.is_file() and sha(file)==r[key],'Changed actual compiler evidence '+name+' '+key)
    text=out.read_text()+err.read_text();need(not FORBIDDEN.search(text),'Strict compiler diagnostic '+name)
    expected=len(re.findall(r'^#print axioms\b',source.read_text(),re.M))
    printed=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',out.read_text())
    none=len(re.findall(r'does not depend on any axioms',out.read_text()))
    need(len(printed)+none==expected,'Incomplete actual printed axiom audit '+name)
    for axes in printed:need({a.strip() for a in axes.split(',') if a.strip()}<=ALLOWED_AXIOMS,'Unverified printed axiom '+name)
    return r


def verify(run):
    plan=json.loads((run/'PLAN.json').read_text())
    need(plan['application_object_fallback'] is False and plan['source_cold'] is True,'Not a true source-cold plan')
    need(sha(Path(plan['context']))==plan['context_sha256'],'Context changed')
    validate_context(Path(plan['context']))
    need(sha(Path(plan['controller']))==plan['controller_sha256'],'Controller changed')
    need(sha(HERE/'compile_verified_batch.py')==plan['helper_sha256'],'Compiler helper changed')
    need(sha(Path(plan['inventory']))==plan['inventory_sha256'],'Pinned inventory changed')
    identities={}
    def index_identity(name,origin,digest):
        item=(str(Path(origin)),digest)
        need(name not in identities or identities[name]==item,'Pinned source identities conflict '+name)
        identities[name]=item
    for r in json.loads(Path(plan['inventory']).read_text())['full_dependency_cone']:index_identity(r['module'],r['source_origin'],r['source_sha256'])
    for path,digest in plan['source_plan_hashes'].items():
        need(sha(Path(path))==digest,'Additional frozen source plan changed')
        extra=json.loads(Path(path).read_text())
        rows=extra.get('source_rows') or [dict(module=extra['module'],origin=extra['source_origin'],source_sha256=extra['source_sha256'])]
        for r in rows:index_identity(r['module'],r['origin'],r['source_sha256'])
        for r in extra.get('accepted_dependencies',[]):index_identity(r['module'],r['source_origin'],r['source_sha256'])
    names={r['module'] for r in plan['source_rows']};need(names==set(identities),'Requested entire pinned source universe differs');need(len(names)==len(plan['source_rows']),'Collapsed module identities')
    for row in plan['source_rows']:
        need((row['origin'],row['source_sha256'])==identities[row['module']],'Pinned written source differs '+row['module'])
        need(all(n.split('.')[0] in GENERIC or n in names for n in row['imports']),'Unlisted application import '+row['module'])
        module_valid(run,row)
    audit=(run/'logs/FFTMainSourceNormAudit.stdout').read_text()
    need('FFT_MAIN_SOURCE_NORM_AUDIT_PASS roots=10' in audit,'Missing complete whole source/Call closure audit')
    need('FFTSourceOutput' in names,'Missing actual source-main/output proof')
    result=run/'RESULT.json'
    if result.is_file():
        r=json.loads(result.read_text());need(r['status']=='PASS_COMPLETE_GENERIC_C_SOURCE_COLD_NOT_LITERAL_ANT','Wrong final result status')
        need(r['plan_sha256']==sha(run/'PLAN.json'),'Final plan hash differs')
        need(r['modules']==len(names),'Final source population differs')
    return len(names)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',type=Path);ap.add_argument('--inventory',type=Path)
    ap.add_argument('--source-plan',type=Path,action='append',default=[])
    ap.add_argument('--root',action='append',default=['FFTMainSourceNormAudit','FFTSourceOutput'])
    ap.add_argument('--run',type=Path);ap.add_argument('--verify-only',type=Path)
    ap.add_argument('--workers',type=int,default=4);ap.add_argument('--worker-memory-gib',type=int,default=64)
    ap.add_argument('--scratch-root',type=Path);ap.add_argument('--scratch-stop-gib',type=int,default=290)
    args=ap.parse_args()
    if args.verify_only:
        need(not args.run,'verify-only cannot start work');print(json.dumps(dict(status='PASS_STRICT_SOURCE_COLD_REVALIDATION',modules=verify(args.verify_only))));return
    need(args.context and args.inventory and args.run and args.scratch_root,'context/inventory/run/scratch-root required')
    need(not args.run.exists(),'Fresh source-cold run required')
    need(1<=args.workers<=4 and 1<=args.worker_memory_gib<=300,'Worker resource policy differs')
    aggregate=args.workers*args.worker_memory_gib*2**30;need(aggregate<=300*2**30,'Aggregate allowance exceeds300GiB')
    ram=available_ram();disk=shutil.disk_usage(args.run.parent).free
    need(ram>=2**40 and ram>=aggregate+256*2**30,'Genuine1TiB availableRAM and256GiB reserve required')
    need(disk>=2**40,'Independent1TiB free disk required')
    need(args.scratch_stop_gib<=290,'Scratch reserve must stop by290GiB')
    scratch=directory_bytes(args.scratch_root);need(scratch<args.scratch_stop_gib*2**30,'Campaign scratch reserve exhausted')
    context=validate_context(args.context);inventory=json.loads(args.inventory.read_text());index={}
    def add(name,origin,digest):
        origin=Path(origin);need(origin.is_file() and sha(origin)==digest,'Pinned source differs '+name)
        if name in index:need(index[name]['source_sha256']==digest and Path(index[name]['origin'])==origin,'Ambiguous written source identity '+name)
        else:index[name]=dict(module=name,origin=str(origin),source_sha256=digest,imports=imports(origin))
    for row in inventory['full_dependency_cone']:add(row['module'],row['source_origin'],row['source_sha256'])
    for path in args.source_plan:
        p=json.loads(path.read_text())
        rows=p.get('source_rows') or [dict(module=p['module'],origin=p['source_origin'],source_sha256=p['source_sha256'])]
        for row in rows:add(row['module'],row['origin'],row['source_sha256'])
        for row in p.get('accepted_dependencies',[]):add(row['module'],row['source_origin'],row['source_sha256'])
    order=[];seen=set();active=set()
    def visit(name):
        if name.split('.')[0] in GENERIC or name in seen:return
        need(name in index,'Missing pinned application source '+name);need(name not in active,'Application import cycle')
        active.add(name)
        for child in index[name]['imports']:visit(child)
        active.remove(name);seen.add(name);order.append(index[name])
    for name in [*args.root,*index]:visit(name)
    need(len(order)>=len(inventory['full_dependency_cone']),'Requested entire source universe not covered')
    args.run.mkdir(parents=True)
    for name in ['source','objects','logs']:(args.run/name).mkdir()
    for row in order:
        target=args.run/'source'/(row['module'].replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes(Path(row['origin']).read_bytes());need(sha(target)==row['source_sha256'],'Snapshot differs')
        row['snapshot']=str(target)
    controller=Path(__file__).resolve();(args.run/'controller.py').write_bytes(controller.read_bytes())
    plan=dict(status='FROZEN_COMPLETE_GENERIC_C_SOURCE_COLD_PLAN',roots=args.root,source_rows=order,
      context=str(args.context.resolve()),context_sha256=sha(args.context),controller=str(controller),controller_sha256=sha(controller),
      helper_sha256=sha(HERE/'compile_verified_batch.py'),inventory=str(args.inventory.resolve()),inventory_sha256=sha(args.inventory),source_plan_hashes={str(p):sha(p) for p in args.source_plan},
      source_cold=True,application_object_fallback=False,workers=args.workers,worker_AS_bytes=args.worker_memory_gib*2**30,
      aggregate_AS_allowance_bytes=aggregate,host_reserve_bytes=256*2**30,admission_MemAvailable_bytes=ram,admission_free_disk_bytes=disk,
      admission_campaign_scratch_bytes=scratch,scratch_root=str(args.scratch_root.resolve()),scratch_stop_bytes=args.scratch_stop_gib*2**30,
      literal_FFT_DAG_recompiled=False)
    atomic(args.run/'PLAN.json',plan)
    env=dict(os.environ,LEAN_PATH=str(args.run/'objects')+':'+context['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1')
    stop=threading.Event();lock=threading.Lock();children={};samples=[];began=time.monotonic();resource_failure=[]
    def terminate_owned():
        with lock:owned=list(children.values())
        for child in owned:
            if child.poll() is None:
                try:os.killpg(child.pid,signal.SIGTERM)
                except ProcessLookupError:pass
    def requested(signum,frame):stop.set();resource_failure.append('signal '+str(signum));terminate_owned()
    signal.signal(signal.SIGTERM,requested);signal.signal(signal.SIGINT,requested)
    def sampler():
        last_disk=-60;usage=scratch
        while not stop.wait(.5):
            elapsed=time.monotonic()-began;ram_now=available_ram()
            if elapsed-last_disk>=60:usage=directory_bytes(args.scratch_root);last_disk=elapsed
            samples.append(dict(seconds=elapsed,RSS_bytes=tree_rss(os.getpid()),MemAvailable_bytes=ram_now,campaign_scratch_bytes=usage))
            if ram_now<256*2**30 or usage>=plan['scratch_stop_bytes']:
                resource_failure.append('host RAM or campaign scratch reserve');stop.set();terminate_owned()
    sampling=threading.Thread(target=sampler,daemon=True);sampling.start()
    def compile_one(row):
        name=row['module'];obj=args.run/'objects'/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        out=args.run/'logs'/(name+'.stdout');err=args.run/'logs'/(name+'.stderr');tm=args.run/'logs'/(name+'.time')
        command=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(args.worker_memory_gib*2**30),'--stack='+str(256*2**20),'--',context['compiler'],'-j1','--root='+str(args.run/'source'),'-o',str(obj),row['snapshot']]
        started=time.monotonic()
        with out.open('xb') as o,err.open('xb') as e:
            child=subprocess.Popen(command,cwd=args.run/'source',env=env,stdout=o,stderr=e,start_new_session=True)
            with lock:children[name]=child
            code=child.wait()
            with lock:children.pop(name,None)
        record=dict(module=name,command=command,exitcode=code,seconds=time.monotonic()-started,stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm))
        atomic(args.run/(name+'.ATTEMPT.json'),record)
        diagnostics=out.read_text()+err.read_text()
        need(code==0 and not FORBIDDEN.search(diagnostics) and obj.is_file(),'Compiler/strict diagnostic failed '+name)
        record['object_sha256']=sha(obj);atomic(args.run/(name+'.COMPILED.json'),record);module_valid(args.run,row)
        return record
    pending={r['module']:r for r in order};running={};done=set();records=[];failure=None
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            while pending or running:
                if stop.is_set():raise RuntimeError('Resource/signal stop')
                for name,row in list(pending.items()):
                    if len(running)>=args.workers:break
                    if all(n.split('.')[0] in GENERIC or n in done for n in row['imports']):
                        running[pool.submit(compile_one,row)]=name;del pending[name]
                need(running,'Dependency scheduler stalled')
                finished,_=concurrent.futures.wait(running,timeout=5,return_when=concurrent.futures.FIRST_COMPLETED)
                for future in finished:
                    name=running.pop(future)
                    try:record=future.result()
                    except Exception:
                        stop.set();terminate_owned();raise
                    done.add(name);records.append(record);print('PASS',name,flush=True)
                state=dict(completed=len(done),total=len(order),running=list(running.values()),seconds=time.monotonic()-began)
                temp=args.run/'PROGRESS.pending';temp.write_text(json.dumps(state)+'\n');os.replace(temp,args.run/'PROGRESS.json')
    except BaseException as exc:
        failure=str(exc);stop.set();terminate_owned()
    finally:
        stop.set();sampling.join();atomic(args.run/'SAMPLED_RESOURCES.json',dict(interval_seconds=.5,sampled_not_exact_peak=True,samples=samples))
    if failure:
        atomic(args.run/'FAILED.json',dict(status='FAILED_COMPLETE_GENERIC_C_SOURCE_COLD',reason=failure,resource_failures=resource_failure,completed=len(done),total=len(order)));raise RuntimeError(failure)
    need(len(done)==len(order),'Incomplete source population')
    verify(args.run)
    rss=[int(v)*1024 for f in (args.run/'logs').glob('*.time') for v in re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)',f.read_text())]
    atomic(args.run/'RESULT.json',dict(status='PASS_COMPLETE_GENERIC_C_SOURCE_COLD_NOT_LITERAL_ANT',modules=len(done),seconds=time.monotonic()-began,
      commands=records,workers=args.workers,worker_AS_bytes=args.worker_memory_gib*2**30,peak_compiler_child_RSS_bytes=max(rss),
      sampled_group_RSS_max_bytes=max((s['RSS_bytes'] for s in samples),default=0),sampled_group_RSS_not_exact_peak=True,
      minimum_MemAvailable_bytes=min((s['MemAvailable_bytes'] for s in samples),default=ram),campaign_scratch_max_sampled_bytes=max((s['campaign_scratch_bytes'] for s in samples),default=scratch),
      directory_allocated_bytes=directory_bytes(args.run),OOM_events=0,resource_failures=resource_failure,plan_sha256=sha(args.run/'PLAN.json'),
      source_cold=True,application_object_fallback=False,literal_FFT_DAG_recompiled=False,fixed_literal_certificate_and_ANT_pending=True))
    print('PASS complete generic actual-C source-cold replay; literal FFT/ANT separately verified',flush=True)


if __name__=='__main__':main()
