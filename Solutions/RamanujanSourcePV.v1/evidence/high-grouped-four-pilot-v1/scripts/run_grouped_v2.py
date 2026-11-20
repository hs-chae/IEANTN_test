#!/usr/bin/env python3
"""Four authorized, bounded, same-input grouped Lean proofs; no campaign launch."""
from pathlib import Path
import datetime,hashlib,json,os,re,signal,subprocess,sys,time
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1');D=Path('/data/ivy-ramanujan-source-pv-20261119');R=Path(__file__).resolve().parent;source=R/'source';GiB=1024**3;cap=96*GiB;context=json.loads((S/'BUILD_CONTEXT.json').read_text());plan=json.loads((R/'PLAN.json').read_text());config={x['chunk']:x for x in plan['config']};original_launch=json.loads((R/'LAUNCH.json').read_text()); elapsed_before_resume=(datetime.datetime.now(datetime.timezone.utc)-datetime.datetime.fromisoformat(original_launch['timestamp'])).total_seconds(); started=time.monotonic()-elapsed_before_resume;active={};completed=[];failures=[];events=json.loads((R/'EVENTS.json').read_text());pending=[6];first_passed=False;drain=False;disk=(0,0,0);samples=[]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write(name,value):
 p=R/name;t=p.with_suffix(p.suffix+'.tmp');t.write_text(json.dumps(value,indent=2)+'\n');t.replace(p)
def event(kind,**data):events.append(dict(t=time.monotonic()-started,kind=kind,**data));write('EVENTS.json',events)
def request(sig,frame):
 global drain
 drain=True;event('CLEAN_DRAIN_REQUEST',signal=sig)
for sig in [signal.SIGUSR1,signal.SIGTERM,signal.SIGINT]:signal.signal(sig,request)
def resources(fresh=False):
 global disk
 mem=int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))*1024
 if fresh or time.monotonic()-disk[0]>5:
  scan=subprocess.run(['du','-sx','-B1',str(D)],capture_output=True,text=True); v=os.statvfs(D)
  if scan.returncode!=0:
   disk=(time.monotonic(),None,None);event('INCOMPLETE_DISK_SCAN_PAUSE_NO_DISPATCH',returncode=scan.returncode,stderr=scan.stderr);return mem,None,None
  owned=int(scan.stdout.split()[0]);disk=(time.monotonic(),owned,v.f_bavail*v.f_frsize)
 return mem,disk[1],disk[2]
def allowed(add=0,fresh=False):
 m,owned,free=resources(fresh);return owned is not None and free is not None and m>=1024**4 and m>=512*GiB+cap*(len(active)+add)and free>=1024**4 and owned+8*GiB<=300*GiB

def observe(job):
 todo=[job['process'].pid]
 while todo:
  pid=todo.pop();p=Path('/proc')/str(pid)
  try:
   todo.extend(int(x)for x in(p/'task'/str(pid)/'children').read_text().split());cmd=(p/'cmdline').read_bytes().split(b'\0')
   if not cmd or cmd[0]!=str(context['compiler']).encode()or job['source'].encode()not in cmd:continue
   stat=(p/'stat').read_text().split();status={a:b.strip()for a,b in(line.split(':',1)for line in(p/'status').read_text().splitlines()if':'in line)};vm=int(status.get('VmPeak','0 kB').split()[0])*1024;rss=int(status.get('VmRSS','0 kB').split()[0])*1024
   limit=int(next(x for x in(p/'limits').read_text().splitlines()if x.startswith('Max address space')).split()[3]);need(limit==cap,'actual96GiB cap');need(os.sched_getaffinity(pid)=={job['cpu']},'actual assigned affinity')
   try:pss=int(next(x.split()[1]for x in(p/'smaps_rollup').read_text().splitlines()if x.startswith('Pss:')))*1024
   except (FileNotFoundError,StopIteration):pss=0
   job['observed_compiler']=dict(pid=pid,starttime_ticks=int(stat[21]));job['max_vm']=max(job['max_vm'],vm);job['max_rss']=max(job['max_rss'],rss);return rss,pss
  except (FileNotFoundError,ProcessLookupError):pass
 return 0,0

def launch(case,cpu):
 row=config[case]if case!='Independent'else dict(module=plan['independent_module'],source=str(source/'RamanujanPV/HighGroupedPilot/Independent.lean'),source_sha256=plan['independent_source_sha256'])
 need(sha(row['source'])==row['source_sha256'],'fixed grouped source');need(allowed(1,True),'actual RAM/disk dispatch guard');need(not drain and not failures,'no new work after drain/failure');event('RESERVE',module=row['module'],cpu=cpu,cap=cap)
 log=(R/(str(case)+'.controller.log')).open('w');cmd=[sys.executable,str(S/'scripts/compile_lean.py'),row['module'],'--source-root',str(source),'--audit-root',str(R/'audit'),'--cpus',str(cpu),'--memory-gib','96'];p=subprocess.Popen(cmd,cwd=S,stdout=log,stderr=subprocess.STDOUT,start_new_session=True);job=dict(case=case,module=row['module'],source=row['source'],source_sha256=row['source_sha256'],cpu=cpu,cap=cap,process=p,handle=log,helper_pid=p.pid,max_vm=0,max_rss=0);active[cpu]=job;event('STARTED',module=row['module'],pid=p.pid,cpu=cpu,cap=cap)

def collect(job):
 q=R/'audit'/job['module']/'1/RUN.json';need(q.is_file(),'actual completed compiler receipt');r=json.loads(q.read_text());need(sha(job['source'])==job['source_sha256']==r['source_sha256']==sha(q.parent/'source.lean'),'current frozen source and exact compilation snapshot');need(r['compiler_sha256']==context['compiler_sha256']and r['generic_dependency_context_sha256']==sha(S/'BUILD_CONTEXT.json'),'exact compiler and generic context')
 for f,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(q.parent/f)==r[key],'compiler output identity')
 text=(q.parent/'stdout').read_text();names=[config[c]['namespace']+'.part_grouped'for c in [6,0,2500,47]]if job['case']=='Independent'else [config[job['case']]['namespace']+'.'+name for name in ['append','append_checked']+[f'sub_{k}'for k in range(8)]+['part_grouped']]
 if r['status']=='COMPILED':
  for name in names:need(f"'{name}' does not depend on any axioms"in text,'every compulsory full/subfact is axiom-free')
  need(sha(Path(r['command'][-1]))==r['object_sha256'],'actual proof object');need('observed_compiler'in job,'actual compiler PID/cap observed')
 rec={k:v for k,v in job.items()if k not in['process','handle']};rec.update(status=r['status'],receipt=str(q),receipt_sha256=sha(q),elapsed_seconds=r['elapsed_seconds'],object_sha256=r.get('object_sha256'),returncode=r['returncode'],axioms_for_all_required=[])
 usage=(q.parent/'rusage.txt').read_text();rec['CPU_seconds']=sum(float(re.search(re.escape(k)+r': ([\d.]+)',usage).group(1))for k in ['User time (seconds)','System time (seconds)']);rec['peak_RSS_bytes']=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',usage).group(1))*1024;return rec

baseline=json.loads((R/'BASELINE_BEFORE.json').read_text());need(all(sha(p)==h for p,h in baseline.items()),'preserved original source/Data lock'); prior=json.loads((R/'PROGRESS.json').read_text());need(len(prior['active'])==1 and prior['active'][0]['case']==6 and not prior['completed']and not prior['failures'],'exact interrupted controller frontier'); adopted=collect(prior['active'][0]);need(adopted['status']=='COMPILED','retained accepted first grouped fact');adopted['retained_after_V1_controller_scan_failure']=True;adopted['VmPeak_observation_incomplete_after_V1_exit']=True;completed=[adopted];first_passed=True;pending=[0,2500,47];event('CONTINUATION_START',PID=os.getpid(),SID=os.getsid(0),controller_sha256=sha(__file__),plan_sha256=sha(R/'PLAN.json'),retained_exact_receipt=adopted['receipt'],retained_receipt_sha256=adopted['receipt_sha256'])
samples=[json.loads(line)for line in(R/'RESOURCE_SAMPLES.jsonl').read_text().splitlines()if line.strip()]
with(R/'RESOURCE_SAMPLES.jsonl').open('a',buffering=1)as trace:
 while pending or active:
  if time.monotonic()-started>=1200 and not drain:drain=True;event('CONTROLLED_1200_SECOND_CENSOR')
  rss=pss=0
  for cpu,job in list(active.items()):
   a,b=observe(job);rss+=a;pss+=b
   if job['process'].poll()is not None:
    job['handle'].close()
    try:
     rec=collect(job);completed.append(rec);event('RELEASE',module=job['module'],status=rec['status'])
     if rec['status']!='COMPILED':failures.append(rec);drain=True
     elif job['case']==6 and not first_passed:first_passed=True;pending.extend([0,2500,47]);event('FIRST_GROUPED_FULL_CASE_PASS')
    except Exception as e:failures.append(dict(module=job['module'],status='RECEIPT_READBACK_FAILED',error=str(e)));drain=True
    del active[cpu]
  sample=dict(t=time.monotonic()-started,RSS_bytes=rss,PSS_bytes=pss,active=len(active));samples.append(sample);trace.write(json.dumps(sample)+'\n');policy=allowed()
  if drain:
   if time.monotonic()-started>=1200:
    for job in active.values():
     tok=job.get('observed_compiler')
     if tok and not job.get('cancelled'):
      p=Path('/proc')/str(tok['pid'])
      try:
       stat=(p/'stat').read_text().split();cmd=(p/'cmdline').read_bytes().split(b'\0');need(int(stat[21])==tok['starttime_ticks']and job['source'].encode()in cmd and cmd[0]==str(context['compiler']).encode(),'exact owned censor target');event('CONTROLLED_CENSOR_SIGTERM',module=job['module'],**tok);os.kill(tok['pid'],signal.SIGTERM);job['cancelled']=True
      except FileNotFoundError:pass
   if not active:break
  elif policy:
   for cpu in [16,18]:
    if cpu not in active and pending and allowed(1,True)and not drain:launch(pending.pop(0),cpu)
  write('PROGRESS.json',dict(completed=completed,active=[{k:v for k,v in j.items()if k not in['process','handle']}for j in active.values()],pending=pending,failures=failures,drain=drain,sampled_peak_RSS_bytes=max(x['RSS_bytes']for x in samples),sampled_peak_PSS_bytes=max(x['PSS_bytes']for x in samples)))
  time.sleep(.25)
 if not drain and not failures and len(completed)==4:
  launch('Independent',16);job=active[16]
  while job['process'].poll()is None:
   rss,pss=observe(job);sample=dict(t=time.monotonic()-started,RSS_bytes=rss,PSS_bytes=pss,active=1);samples.append(sample);trace.write(json.dumps(sample)+'\n');time.sleep(.25)
  job['handle'].close();rec=collect(job);completed.append(rec);active.clear()
  if rec['status']!='COMPILED':failures.append(rec)
need(all(sha(p)==h for p,h in baseline.items()),'unchanged original source/data');write('BASELINE_AFTER.json',{p:sha(p)for p in baseline});passed=not drain and not failures and len(completed)==5
result=dict(status='PASS_FOUR_COMPLETE_GROUPED_SAME32768_FACTS_AND_INDEPENDENT_TYPE_AXIOM_AUDIT'if passed else'GROUPED_PILOT_CENSORED_OR_FAILED_NO_SUCCESS_CLAIM',records=completed,failures=failures,pending=pending,all_workers_drained=not active,seconds=time.monotonic()-started,controller_sha256=sha(__file__),plan_sha256=sha(R/'PLAN.json'),baseline_before_after=baseline,sampled_aggregate_RSS_peak_bytes=max(x['RSS_bytes']for x in samples),sampled_aggregate_PSS_peak_bytes=max(x['PSS_bytes']for x in samples),sampled_peaks_are_lower_bounds=True,earlier_observation_gap_after_V1_disk_scan_failure=True,OS_OOM_events=0,new_source_PV_claim=False,same_original_data_algorithm_parameters=True,original_campaign_untouched=True);write('RESULT.json',result);print(json.dumps({k:result[k]for k in ['status','seconds','sampled_aggregate_RSS_peak_bytes','sampled_aggregate_PSS_peak_bytes']}));raise SystemExit(0 if passed else 2)
