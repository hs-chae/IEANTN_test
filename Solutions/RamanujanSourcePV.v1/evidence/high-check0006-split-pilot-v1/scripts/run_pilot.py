#!/usr/bin/env python3
"""Bounded exact same-input eight-way Lean proof-decomposition pilot only."""
from pathlib import Path
import datetime,hashlib,json,os,resource,signal,subprocess,sys,time
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1');D=Path('/data/ivy-ramanujan-source-pv-20261119');R=D/'high-check0006-split-pilot-v1';source=R/'source';cpus=[16,18];GiB=1024**3;cap=96*GiB;ctx=json.loads((S/'BUILD_CONTEXT.json').read_text());started=time.monotonic();active={};completed=[];failures=[];pending=list(range(8));drain=False;events=[];samples=[];lastdisk=(0,None,None)
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(name,d):
 p=R/name;t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(d,indent=2)+'\n');t.replace(p)
def event(kind,**kw):events.append(dict(t=time.monotonic()-started,kind=kind,**kw));write('EVENTS.json',events)
def request(sig,frame):
 global drain
 drain=True;event('CLEAN_DRAIN_REQUEST',signal=sig)
for sig in [signal.SIGUSR1,signal.SIGTERM,signal.SIGINT]:signal.signal(sig,request)
def resources(fresh=False):
 global lastdisk
 mem=int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))*1024
 if fresh or time.monotonic()-lastdisk[0]>5:
  owned=int(subprocess.check_output(['du','-sx','-B1',str(D)],text=True).split()[0]);free=os.statvfs(D).f_bavail*os.statvfs(D).f_frsize;lastdisk=(time.monotonic(),owned,free)
 return mem,lastdisk[1],lastdisk[2]
def allowed(add=0,fresh=False):
 m,owned,free=resources(fresh);return m>=1024**4 and m>=512*GiB+cap*(len(active)+add)and free>=1024**4 and owned+8*GiB<=300*GiB

def descendants(pid):
 todo=[pid];seen=[]
 while todo:
  p=todo.pop()
  try:todo.extend(int(x)for x in Path(f'/proc/{p}/task/{p}/children').read_text().split());seen.append(p)
  except FileNotFoundError:pass
 return seen

def observe(job):
 for pid in descendants(job['process'].pid):
  p=Path('/proc')/str(pid)
  try:
   cmd=(p/'cmdline').read_bytes().split(b'\0');stat=(p/'stat').read_text().split()
   if cmd[0]!=str(ctx['compiler']).encode()or str(job['source']).encode()not in cmd:continue
   status={a.strip():b.strip()for a,b in(line.split(':',1)for line in(p/'status').read_text().splitlines()if':'in line)}
   vm=int(status.get('VmPeak','0 kB').split()[0])*1024;rss=int(status.get('VmRSS','0 kB').split()[0])*1024
   limits=(p/'limits').read_text();limit=int(next(x for x in limits.splitlines()if x.startswith('Max address space')).split()[3]);need(limit==job['cap'],'actual compiler RLIMIT cap');need(os.sched_getaffinity(pid)=={job['cpu']},'actual assigned CPU affinity')
   token=dict(pid=pid,starttime_ticks=int(stat[21]));job['observed_compiler']=token;job['max_vm']=max(job['max_vm'],vm);job['max_rss']=max(job['max_rss'],rss)
   return rss
  except (FileNotFoundError,ProcessLookupError,IndexError):pass
 return 0

def finish(job):
 p=R/'audit'/job['module']/'1/RUN.json';need(p.is_file(),'compiler completion receipt exists');r=json.loads(p.read_text());q=p.parent
 for name,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(q/name)==r[key],'exact compiler output')
 need(sha(job['source'])==r['source_sha256']==job['source_sha256']==sha(q/'source.lean'),'exact frozen application source')
 need(r['compiler_sha256']==ctx['compiler_sha256']and r['generic_dependency_context_sha256']==sha(S/'BUILD_CONTEXT.json'),'pinned proof context')
 text=(q/'stdout').read_text();expected='RamanujanPV.HighCheck0006SplitPilot.'+job['theorem'];empty=f"'{expected}' does not depend on any axioms"
 if r['status']=='COMPILED':
  need(empty in text,'independently compulsory axiom-free theorem');need(sha(Path(r['command'][-1]))==r['object_sha256'],'actual output object')
 record={k:v for k,v in job.items()if k not in ['process','handle']};record.update(receipt=str(p),receipt_sha256=sha(p),status=r['status'],seconds=r['elapsed_seconds'],stdout_sha256=r['stdout_sha256'],object_sha256=r.get('object_sha256'),returncode=r['returncode'])
 usage=(q/'rusage.txt').read_text()
 for label,key in [('User time (seconds)','user_seconds'),('System time (seconds)','system_seconds'),('Maximum resident set size (kbytes)','peak_rss_kib')]:
  import re
  match=re.search(re.escape(label)+r': ([\d.]+)',usage);record[key]=float(match.group(1))if match else None
 return record

def launch(index,cpu):
 name='Final'if index=='Final'else'Check'+str(index);module='RamanujanPV.HighCheck0006SplitPilot.'+name;src=source/Path(*module.split('.')).with_suffix('.lean');memory=48*GiB if index=='Final'else cap
 need(src.is_file(),'fixed selected source');need(allowed(1,True),'actual dispatch resource guard');need(not drain,'no dispatch after drain');event('RESERVE',module=module,cap=memory,cpu=cpu)
 log=(R/(name+'.controller.log')).open('w');cmd=[sys.executable,str(S/'scripts/compile_lean.py'),module,'--source-root',str(source),'--audit-root',str(R/'audit'),'--cpus',str(cpu),'--memory-gib',str(memory//GiB)]
 process=subprocess.Popen(cmd,cwd=S,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);job=dict(module=module,source=src,source_sha256=sha(src),theorem='part_0006_split'if index=='Final'else'chunk_'+str(index),cpu=cpu,cap=memory,process=process,handle=log,max_vm=0,max_rss=0,helper_pid=process.pid)
 # Every serialized state uses strings, not private process objects.
 job['source']=str(src);active[cpu]=job;event('STARTED',module=module,pid=process.pid,cpu=cpu,cap=memory)

need(not(R/'RESULT.json').exists(),'fresh pilot result');bridge=R/'audit/RamanujanPV.HighCheck0006SplitPilot.Bridge/3';b=json.loads((bridge/'RUN.json').read_text());need(b['status']=='COMPILED','accepted pure bridge');text=(bridge/'stdout').read_text();need("'RamanujanPV.HighCheck0006SplitPilot.append' does not depend on any axioms"in text and"'RamanujanPV.HighCheck0006SplitPilot.append_checked' does not depend on any axioms"in text,'axiom-free Boolean composition')
shared_paths=[D/'high-transition-count-proposal-v1/proposal/source/RamanujanPV/HighTransitionCount/Data.lean',D/'lean/RamanujanPV/HighTransitionCount/Data.olean',D/'high-transition-count-proposal-v1/proposal/source/RamanujanPV/HighTransitionCount/Check0006.lean',D/'lean/RamanujanPV/HighTransitionCount/Check0006.olean']; shared_hashes={str(p):sha(p) for p in shared_paths};write('UNCHANGED_BASELINE_BEFORE.json',shared_hashes)
plan=json.loads((R/'PLAN.json').read_text());plan['status']='ACTUALLY_EXECUTING_REFINED_AXIOM_FREE_BRIDGE';plan['bridge_receipt']=str(bridge/'RUN.json');plan['bridge_receipt_sha256']=sha(bridge/'RUN.json');plan['controller_sha256']=sha(__file__);plan['source_manifest']=[dict(module='RamanujanPV.HighCheck0006SplitPilot.'+p.stem,source=str(p),sha256=sha(p))for p in sorted((source/'RamanujanPV/HighCheck0006SplitPilot').glob('*.lean'))];write('PLAN_REFINED.json',plan)
need(allowed(0,True),'startup resource guard');event('START',PID=os.getpid(),source_manifest_sha256=sha(R/'PLAN_REFINED.json'))
while pending or active:
 if time.monotonic()-started>=1200 and not drain:drain=True;event('CONTROLLED_1200_SECOND_CENSOR')
 rss=0
 for cpu,job in list(active.items()):
  rss+=observe(job)
  if job['process'].poll()is not None:
   job['handle'].close()
   try:rec=finish(job);completed.append(rec);event('RELEASE',module=job['module'],status=rec['status'])
   except Exception as e:rec=dict(module=job['module'],status='FAILED_RECEIPT_READBACK',error=str(e));failures.append(rec);drain=True
   if rec['status']!='COMPILED':failures.append(rec);drain=True
   del active[cpu]
 samples.append(dict(t=time.monotonic()-started,observed_aggregate_worker_RSS_bytes=rss,active=len(active)))
 if drain:
  # No baseline process is signalled. At deadline only verified owned Lean children are terminated.
  if time.monotonic()-started>=1200:
   for job in active.values():
    token=job.get('observed_compiler')
    if token and not job.get('cancelled'):
     p=Path('/proc')/str(token['pid'])
     try:
      st=(p/'stat').read_text().split();cmd=(p/'cmdline').read_bytes().split(b'\0');need(int(st[21])==token['starttime_ticks']and str(job['source']).encode()in cmd and cmd[0]==str(ctx['compiler']).encode(),'exact owned cancellation target');event('CENSORED_OWNED_LEAN_SIGTERM',module=job['module'],**token);os.kill(token['pid'],signal.SIGTERM);job['cancelled']=True
     except FileNotFoundError:pass
  if not active:break
 else:
  for cpu in cpus:
   if cpu not in active and pending and allowed(1,True)and not drain:launch(pending.pop(0),cpu)
 write('PROGRESS.json',dict(completed=completed,pending=pending,active=[{k:v for k,v in j.items()if k not in['process','handle']}for j in active.values()],failures=failures,drain=drain))
 time.sleep(0.25)
if not drain and not failures and len(completed)==8:
 launch('Final',16)
 job=active[16]
 while job['process'].poll()is None:observe(job);time.sleep(0.25)
 job['handle'].close();rec=finish(job);completed.append(rec);active.clear();need(rec['status']=='COMPILED','exact final combined theorem')
need(all(sha(p)==h for p,h in shared_hashes.items()),'unchanged baseline source/Data/Check0006 objects');write('UNCHANGED_BASELINE_AFTER.json',{p:sha(p) for p in shared_hashes})
status='PASS_ALL_EIGHT_SAME_INPUT_CHECKS_AND_EXACT_AXIOM_FREE_COMPOSITION'if not drain and not failures and len(completed)==9 else'CONTROLLED_CENSORED_OR_FAILED_PILOT_NO_SUCCESS_CLAIM'
result=dict(status=status,plan_sha256=sha(R/'PLAN_REFINED.json'),controller_sha256=sha(__file__),seconds=time.monotonic()-started,original_seconds=plan['original_elapsed_seconds'],records=completed,failures=failures,pending=pending,all_active_drained=not active,resource_samples=samples,sampled_aggregate_RSS_peak_bytes=max((x['observed_aggregate_worker_RSS_bytes']for x in samples),default=0),sampled_peak_is_lower_bound=True,same_original_mathematical_predicate=plan['same_predicate'],no_source_or_data_or_baseline_controller_changes=True,no_source_PV_claim_for_proof_representation=True);write('RESULT.json',result);print(json.dumps({k:result[k]for k in ['status','seconds','original_seconds','sampled_aggregate_RSS_peak_bytes']}));raise SystemExit(0 if status.startswith('PASS_') else 2)
