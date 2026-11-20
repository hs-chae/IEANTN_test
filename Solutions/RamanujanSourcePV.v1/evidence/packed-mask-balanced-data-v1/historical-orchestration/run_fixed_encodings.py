from pathlib import Path
import concurrent.futures,subprocess,sys,time,json,os,signal,hashlib
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1')
sys.path.insert(0,str(S/'scripts'))
from execute_packed_mask_chunks import guard,atomic
D=Path('/data/ivy-ramanujan-source-pv-20261119/packed-mask-balanced-data-scout');root=D/'production-v1';src=root/'source';out=root/'run-v1';out.mkdir();prefix='RamanujanPV.PackedMaskDataEncoding'
manifest=json.loads((root/'PROPOSAL.json').read_text());recordmap={x['module']:x for x in manifest['records']}
expected=set(recordmap);tasks={x['module']:set()for x in manifest['records']}
for w in[256,1024,4096]:tasks[prefix+f'.W{w}.Equality']={prefix+'.BaselineData',prefix+f'.W{w}.Data'}
priority=[prefix+'.BaselineData']+[prefix+f'.W{w}.Data'for w in[256,1024,4096]]+[prefix+f'.W{w}.Equality'for w in[256,1024,4096]]
completed=set();rows=[];failures=[];active={};free=[32,33];start=time.time();deadline=start+1200

def launch(module,cpu):
 resource=guard(96<<30);p=Path(recordmap[module]['source'])
 if hashlib.sha256(p.read_bytes()).hexdigest()!=recordmap[module]['sha256']:raise ValueError('source changed')
 job=out/'jobs'/module;job.mkdir(parents=True);command=[sys.executable,str(S/'scripts/compile_lean.py'),module,'--source-root',str(src),'--audit-root',str(out/'audit'),'--cpus',str(cpu),'--memory-gib','48']
 begin=time.monotonic()
 with(job/'stdout').open('wb')as stdout,(job/'stderr').open('wb')as stderr:
  child=subprocess.Popen(command,cwd=S,stdout=stdout,stderr=stderr,start_new_session=True)
  atomic(job/'START.json',dict(pid=child.pid,start_ticks=Path('/proc',str(child.pid),'stat').read_text().split()[21],command=command,resource=resource,source_sha256=recordmap[module]['sha256']))
  while child.poll()is None:
   if time.time()>=deadline:os.killpg(child.pid,signal.SIGTERM);child.wait();break
   time.sleep(.5)
 row=dict(module=module,command=command,returncode=child.returncode,wall_seconds=time.monotonic()-begin,job=str(job))
 if child.returncode==0:
  summary=json.loads((job/'stdout').read_text().strip().splitlines()[-1]);row['receipt']=str(Path(summary['audit'])/'RUN.json')
 atomic(job/'OUTCOME.json',row);return row
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
 while tasks or active:
  if time.time()<deadline:
   try:
    guard(96<<30)
    for module in priority:
     if not free:break
     if module in tasks and tasks[module]<=completed:
      cpu=free.pop(0);tasks.pop(module);active[pool.submit(launch,module,cpu)]=(module,cpu)
   except BaseException as error:failures.append(dict(resource_guard=repr(error)));tasks.clear()
  else:tasks.clear()
  done,_=concurrent.futures.wait(active,timeout=1,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in done:
   module,cpu=active.pop(f);free.append(cpu)
   try:
    r=f.result();rows.append(r)
    if r['returncode']==0:completed.add(module)
    else:failures.append(r)
   except BaseException as error:failures.append(dict(module=module,error=repr(error)))
  atomic(out/'PROGRESS.json',dict(status='RAW_FIXED_JOB_OBSERVATION_NOT_INDEPENDENT_ACCEPTANCE',active=[v[0]for v in active.values()],records=rows,failures=failures,completed=sorted(completed),pending=sorted(tasks),elapsed_seconds=time.time()-start))
  if not active and tasks and not any(deps<=completed for deps in tasks.values()):break
atomic(out/'RAW_RESULT.json',dict(status='FIXED_ENCODING_JOBS_DRAINED_NOT_INDEPENDENT_ACCEPTANCE',records=rows,failures=failures,completed=sorted(completed),unexecuted=sorted(expected-completed),elapsed_seconds=time.time()-start))
