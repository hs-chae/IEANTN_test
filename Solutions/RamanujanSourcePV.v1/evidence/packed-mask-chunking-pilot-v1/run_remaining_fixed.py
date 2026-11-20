from pathlib import Path
import sys,os,subprocess,concurrent.futures,json,time,datetime,signal,hashlib
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1')
sys.path.insert(0,str(S/'scripts'))
from execute_packed_mask_chunks import guard,read_record,atomic
D=Path('/data/ivy-ramanujan-source-pv-20261119/packed-mask-chunking-pilot');src=D/'production-v3/source';out=D/'direct-remaining-v1';out.mkdir()
end=datetime.datetime(2026,11,20,9,14,tzinfo=datetime.timezone.utc).timestamp()
prefix='RamanujanPV.PackedMaskChunkPilot';tasks={};completed=set();rows=[];failed=[];starts={}
for k in [2,8,16]:
 data=prefix+f'.K{k}.Data';tasks[data]=set()
 for i in range(k):tasks[prefix+f'.K{k}.Check{i:04d}']={data}
 tasks[prefix+f'.K{k}.Final']={prefix+f'.K{k}.Check{i:04d}'for i in range(k)}
priority=[prefix+'.K16.Data',prefix+'.K2.Data']+[prefix+f'.K2.Check{i:04d}'for i in range(2)]+[prefix+'.K2.Final',prefix+'.K8.Data']+[prefix+f'.K8.Check{i:04d}'for i in range(8)]+[prefix+'.K8.Final']+[prefix+f'.K16.Check{i:04d}'for i in range(16)]+[prefix+'.K16.Final']
def launch(module,cpu):
 pre=guard(96<<30);command=[sys.executable,str(S/'scripts/compile_lean.py'),module,'--source-root',str(src),'--audit-root',str(out/'audit'),'--cpus',str(cpu),'--memory-gib','48']
 log=out/'jobs'/module;log.mkdir(parents=True);start=time.monotonic();starts[module]=time.time()
 with(log/'stdout').open('wb')as stdout,(log/'stderr').open('wb')as stderr:
  child=subprocess.Popen(command,cwd=S,stdout=stdout,stderr=stderr,start_new_session=True)
  atomic(log/'START.json',dict(module=module,pid=child.pid,start_ticks=Path('/proc',str(child.pid),'stat').read_text().split()[21],command=command,resource=pre))
  while child.poll()is None:
   if time.time()>=end:
    os.killpg(child.pid,signal.SIGTERM);child.wait();break
   time.sleep(.5)
 record=dict(module=module,command=command,returncode=child.returncode,elapsed_seconds=time.monotonic()-start,job_log=str(log),cpu=cpu)
 if child.returncode==0:
  summary=json.loads((log/'stdout').read_text().strip().splitlines()[-1]);r=read_record(Path(summary['audit'])/'RUN.json',reports_required=not module.endswith('.Data'));record['compiler_receipt']=r
 atomic(log/'OUTCOME.json',record);return record
active={};free=[33,32];begin=time.time()
with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:
 while tasks or active:
  if time.time()<end:
   try:
    guard(96<<30)
    for module in priority:
     if not free:break
     if module in tasks and tasks[module]<=completed:
      cpu=free.pop(0);tasks.pop(module);active[pool.submit(launch,module,cpu)]=(module,cpu)
   except BaseException as error:failed.append(dict(resource_guard=repr(error)));tasks.clear()
  else:tasks.clear()
  done,_=concurrent.futures.wait(active,timeout=1,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in done:
   module,cpu=active.pop(future);free.append(cpu)
   try:
    r=future.result();rows.append(r)
    if r['returncode']==0:completed.add(module)
    else:
     failed.append(r)
     for name in list(tasks):
      if module in tasks[name]:tasks.pop(name)
   except BaseException as error:failed.append(dict(module=module,error=repr(error)))
  atomic(out/'PROGRESS.json',dict(status='RAW_EXECUTION_OBSERVATION_NOT_INDEPENDENT_ACCEPTANCE',completed=sorted(completed),active=[v[0]for v in active.values()],pending=sorted(tasks),records=rows,failures=failed,elapsed_seconds=time.time()-begin))
  if not active and tasks and not any(deps<=completed for deps in tasks.values()):break
atomic(out/'RAW_RESULT.json',dict(status='FIXED_BOUNDED_JOBS_DRAINED_NOT_INDEPENDENT_ACCEPTANCE',records=rows,failures=failed,completed=sorted(completed),unexecuted=sorted(tasks),elapsed_seconds=time.time()-begin))
