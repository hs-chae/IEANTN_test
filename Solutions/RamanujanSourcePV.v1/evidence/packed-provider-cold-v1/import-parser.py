#!/usr/bin/env python3
"""Rebuild only the selected QRH->pi144 source closure, with no old app objects.

Generic dependencies are pinned by BUILD_CONTEXT.json. Module resolution follows
local Lake path requirements. The new application additionally imports the two
explicit legacy projects recorded in EXTRA_APPLICATION_PROJECTS. This helper is
separate from reproduce_lean.py and emits local research build records only.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, threading, time, tomllib
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

S=Path(__file__).resolve().parents[1]
NETWORK=S.parents[1]
EXTRA_APPLICATION_PROJECTS=[NETWORK/'Solutions/QRHPropagation.v2',NETWORK/'Solutions/CH2.v6']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(ok,message):
 if not ok:raise ValueError(message)
def atomic(p,obj):
 q=p.with_suffix(p.suffix+'.tmp');q.write_text(json.dumps(obj,indent=2)+'\n');q.replace(p)
def imports(source):
 text=source.read_text();clean=[];i=0;depth=0;string=False
 while i<len(text):
  if depth:
   if text.startswith('/-',i):depth+=1;i+=2
   elif text.startswith('-/',i):depth-=1;i+=2
   else:
    if text[i]=='\n':clean.append('\n')
    i+=1
  elif string:
   if text[i]=='\\':i+=2
   elif text[i]=='"':string=False;i+=1
   else:
    if text[i]=='\n':clean.append('\n')
    i+=1
  elif text.startswith('/-',i):depth=1;i+=2
  elif text.startswith('--',i):
   j=text.find('\n',i);i=len(text)if j<0 else j
  elif text[i]=='"':string=True;i+=1
  else:clean.append(text[i]);i+=1
 need(depth==0,'unterminated Lean block comment '+str(source))
 result=[]
 for line in ''.join(clean).split('\n'):
  m=re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+?)\s*$',line)
  if m:
   for name in m.group(1).split():
    need(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*',name)is not None,'unsupported module spelling '+name)
    result.append(name)
 return result

def main():
 p=argparse.ArgumentParser(allow_abbrev=False)
 p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json')
 p.add_argument('--out',type=Path,required=True)
 p.add_argument('--root',action='append',default=[])
 p.add_argument('--run',action='store_true')
 p.add_argument('--cpus',default='8,9,10,11');p.add_argument('--jobs',type=int,default=4)
 a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh experiment-owned output directory required')
 c=json.loads(a.context.read_text());compiler=Path(c['compiler'])
 need(sha(compiler)==c['compiler_sha256'],'pinned Lean compiler')
 generic=[]
 for d in c['generic_dependencies']:
  if not d['library_present']:continue
  root=Path(d['path'])
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==d['revision'],'generic pin '+d['name'])
  need(not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True),'generic tracked-source identity '+d['name'])
  generic.append(Path(d['library']))
 toolchain=compiler.parent.parent/'lib/lean'
 cpus=[int(t)for t in a.cpus.split(',')]
 need(len(set(cpus))==len(cpus)and set(cpus)<=os.sched_getaffinity(0),'available distinct CPUs')
 need(1<=a.jobs<=len(cpus)<=4,'bounded worker count')
 project_cache={}
 def projects(project):
  project=project.resolve()
  if project in project_cache:return project_cache[project]
  file=project/'lakefile.toml';need(file.is_file(),'Lake project '+str(project))
  data=tomllib.loads(file.read_text());order=[project]
  for dep in data.get('require',[]):
   if 'path'in dep:
    for q in projects(project/dep['path']):
     if q not in order:order.append(q)
  if project==S:
   for q0 in EXTRA_APPLICATION_PROJECTS:
    for q in projects(q0):
     if q not in order:order.append(q)
  project_cache[project]=order;return order
 modules={};visiting=set();order=[]
 def resolve(module,project):
  rel=Path(*module.split('.')).with_suffix('.lean')
  candidates=[NETWORK]if module.startswith('IEANTN.')else projects(project)
  for base in candidates:
   src=base/rel
   if src.is_file():return base,src
  obj=rel.with_suffix('.olean')
  need(any((q/obj).is_file()for q in [*generic,toolchain]),'unresolved import '+module+' from '+str(project))
  return None,None
 def visit(module,project):
  base,src=resolve(module,project)
  if src is None:return
  if module in modules:
   need(modules[module]['source']==str(src),'ambiguous source identity for '+module)
   return
  need(module not in visiting,'import cycle '+module);visiting.add(module)
  deps=imports(src)
  for dep in deps:visit(dep,base)
  visiting.remove(module)
  rec={'module':module,'base':str(base),'source':str(src),'source_sha256':sha(src),'imports':deps}
  modules[module]=rec;order.append(module)
 roots=a.root or['RamanujanPV.QRHClosure']
 for module in roots:visit(module,S)
 out.mkdir(parents=True);objects=out/'lean';objects.mkdir();audit=out/'audit';audit.mkdir()
 manifest={'status':'PLANNED','roots':roots,'module_count':len(order),'compiler_sha256':c['compiler_sha256'],'context_sha256':sha(a.context),'generic_libraries':[str(x)for x in generic],'old_application_objects_used':False,'application_object_root':str(objects),'ordered_modules':[modules[m]for m in order],'cpus':cpus,'max_parallel_workers':a.jobs,'per_worker_memory_bytes':48<<30,'resolver_extra_projects':[str(x)for x in EXTRA_APPLICATION_PROJECTS]}
 manifest['initial_machine_resources']={'meminfo':{k:int(v.split()[0])*1024 for k,v in (line.split(':',1)for line in Path('/proc/meminfo').read_text().split('\n')if ':'in line)if k in ['MemTotal','MemAvailable','SwapFree']},'disk':dict(zip(['total','used','free'],shutil.disk_usage(out.parent)))}
 atomic(out/'PLAN.json',manifest);print(json.dumps({'status':'PLANNED','modules':len(order),'out':str(out)}),flush=True)
 if not a.run:return
 env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(objects),*[str(x)for x in generic]]))
 live={};live_lock=threading.Lock();stopping=threading.Event()
 def stop_jobs(signum,frame):
  stopping.set()
  with live_lock:
   pids=list(live)
   for pid in pids:
    try:os.killpg(pid,signal.SIGTERM)
    except ProcessLookupError:pass
  atomic(out/'INTERRUPTED.json',{'status':'INTERRUPTED_JOBS_TERMINATED','signal':signum,'process_groups':pids,'old_application_objects_used':False})
  raise KeyboardInterrupt
 signal.signal(signal.SIGINT,stop_jobs);signal.signal(signal.SIGTERM,stop_jobs)
 completed={};pending=set(order);running={};started=time.monotonic();last=started
 def compile_one(module,cpu):
  row=modules[module];src=Path(row['source']);need(sha(src)==row['source_sha256'],'source changed before compile '+module)
  d=audit/module;d.mkdir();(d/'source.lean').write_bytes(src.read_bytes());obj=objects/Path(*module.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  cmd=[str(compiler),'-j1','-R',row['base'],str(src),'-o',str(obj)];t=time.monotonic()
  with(d/'stdout').open('wb')as so,(d/'stderr').open('wb')as se:
   full=['/usr/bin/time','-v','-o',str(d/'rusage'),'/usr/bin/prlimit',f'--as={48<<30}','--','/usr/bin/taskset','-c',str(cpu),*cmd]
   with live_lock:
    need(not stopping.is_set(),'study stopping')
    child=subprocess.Popen(full,cwd=row['base'],env=env,stdout=so,stderr=se,start_new_session=True)
    live[child.pid]=module
   code=child.wait()
   with live_lock:live.pop(child.pid,None)
  need(sha(src)==row['source_sha256'],'source changed during compile '+module)
  rec={**row,'exit_code':code,'seconds':time.monotonic()-t,'cpu':cpu,'command':cmd,'stdout_sha256':sha(d/'stdout'),'stderr_sha256':sha(d/'stderr'),'rusage_sha256':sha(d/'rusage')}
  if code==0:rec['object_sha256']=sha(obj)
  atomic(d/'RUN.json',rec);return rec
 with ThreadPoolExecutor(max_workers=a.jobs)as pool:
  while pending or running:
   free=[cpu for cpu in cpus[:a.jobs]if cpu not in running.values()]
   ready=[m for m in order if m in pending and all(d not in modules or d in completed for d in modules[m]['imports'])]
   for module,cpu in zip(ready,free):
    pending.remove(module);f=pool.submit(compile_one,module,cpu);running[f]=cpu
   need(running or not pending,'blocked dependency graph')
   finished,_=wait(running,timeout=20,return_when=FIRST_COMPLETED)
   for future in finished:
    cpu=running.pop(future);row=future.result();module=row['module']
    if row['exit_code']:
     atomic(out/'RESULT.json',{'status':'FAILED_ATTEMPT_PRESERVED','failed':row,'completed':list(completed),'pending_count':len(pending),'elapsed_seconds':time.monotonic()-started,'old_application_objects_used':False})
     print(json.dumps({'status':'FAILED','module':module,'completed':len(completed),'out':str(out)}),flush=True)
     for f in running:f.result()
     return 1
    completed[module]=row
   now=time.monotonic()
   if now-last>=20 or not(pending or running):
    state={'status':'RUNNING'if pending or running else'COMPILED','completed':len(completed),'total':len(order),'running':len(running),'elapsed_seconds':now-started}
    atomic(out/'PROGRESS.json',state);print(json.dumps(state),flush=True);last=now
 atomic(out/'RESULT.json',{'status':'FRESH_QRH_CLOSURE_BUILD_PASS','roots':roots,'records':[completed[m]for m in order],'elapsed_seconds':time.monotonic()-started,'old_application_objects_used':False})
 return 0
if __name__=='__main__':raise SystemExit(main())
