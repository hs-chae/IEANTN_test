#!/usr/bin/env python3
"""Read-only observation of the two authorized study units; no worker messages."""
from pathlib import Path
import datetime,json,os,subprocess,time,hashlib
D=Path('/data/ivy-rh-propagation-20261120');R=Path(__file__).resolve().parents[1]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def atomic(p,d):
 t=p.with_suffix('.pending');t.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n');os.replace(t,p)
def disk(root,seconds=3):
 start=time.monotonic();logical=allocated=count=0;complete=True
 try:
  for base,dirs,files in os.walk(root,followlinks=False):
   for name in files:
    p=Path(base,name)
    try:
     if p.is_symlink():continue
     s=p.stat();logical+=s.st_size;allocated+=s.st_blocks*512;count+=1
    except OSError:continue
   if time.monotonic()-start>seconds:complete=False;break
 except OSError:complete=False
 return {'logical_bytes':logical,'allocated_bytes':allocated,'files':count,'complete':complete,'seconds':time.monotonic()-start,'location':str(root)}
def procs(cgroup):
 rows=[];pids=[]
 for path in cgroup.rglob('cgroup.procs'):
  try:pids.extend(int(p)for p in path.read_text().split())
  except OSError:continue
 for pid in sorted(set(pids)):
  try:
   text=Path('/proc',str(pid),'status').read_text();s={line.split(':',1)[0]:line.split(':',1)[1].strip()for line in text.splitlines()if':'in line};rss=int(s.get('VmRSS','0 kB').split()[0])*1024
   pss=None
   try:
    ps=Path('/proc',str(pid),'smaps_rollup').read_text();pss=sum(int(line.split()[1])*1024 for line in ps.splitlines()if line.startswith('Pss:'))
   except OSError:pass
   rows.append({'pid':pid,'name':s.get('Name'),'rss_bytes':rss,'pss_bytes':pss})
  except (OSError,ValueError):continue
 return rows
summary={'schema':'RH_PAIR_RESOURCE_OBSERVATION_V1','started_utc':now(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'kernel_peak_memory_available':False,'sampled_peaks_are_lower_bounds':True,'arms':{a:{'max_sampled_cgroup_memory_current':0,'max_sampled_aggregate_RSS':0,'max_sampled_aggregate_PSS':0,'max_sampled_private_work_logical_bytes':0,'memory_events_last':None,'samples':0}for a in ['NL_RH','IEANTN_RH']}}
(D/'observation').mkdir(exist_ok=True);last_disk=0
while True:
 all_terminal=True
 for arm in ['NL_RH','IEANTN_RH']:
  unit='ivy-rh-'+arm.replace('_','-').lower()+'-primary-v1';run=D/'runs'/('primary-'+arm+'-v1')
  p=subprocess.run(['systemctl','--user','show',unit,'--property=ActiveState,SubState,MainPID,ControlGroup,Result,ExecMainStatus'],capture_output=True,text=True);u=dict(line.split('=',1)for line in p.stdout.splitlines()if'='in line)
  g=Path('/sys/fs/cgroup')/u.get('ControlGroup','').lstrip('/');s={'utc':now(),'arm':arm,'unit':u,'pids':[]}
  if u.get('ActiveState')=='active'and u.get('ControlGroup'):
   all_terminal=False;s['pids']=procs(g)
   for name in ['memory.current','memory.max','memory.swap.max','memory.events','cpu.stat']:
    try:s[name]=(g/name).read_text()
    except OSError:s[name]=None
   a=summary['arms'][arm];a['samples']+=1
   if s.get('memory.current'):a['max_sampled_cgroup_memory_current']=max(a['max_sampled_cgroup_memory_current'],int(s['memory.current']))
   a['max_sampled_aggregate_RSS']=max(a['max_sampled_aggregate_RSS'],sum(row['rss_bytes']for row in s['pids']))
   a['max_sampled_aggregate_PSS']=max(a['max_sampled_aggregate_PSS'],sum(row['pss_bytes']or 0 for row in s['pids']))
   a['memory_events_last']=s.get('memory.events');a['cpu_stat_last']=s.get('cpu.stat');a['last_observed_utc']=s['utc']
   if time.monotonic()-last_disk>=60:
    roots=set()
    for proc in s['pids']:
     root=Path('/proc',str(proc['pid']),'root/work')
     try:
      st=root.stat();key=(st.st_dev,st.st_ino)
      if key in roots:continue
      roots.add(key);d=disk(root);s.setdefault('private_work_disk_observations',[]).append(d)
      if d['complete']:a['max_sampled_private_work_logical_bytes']=max(a['max_sampled_private_work_logical_bytes'],d['logical_bytes'])
     except OSError:continue
  if (run/'result.json').exists():
   data=json.loads((run/'result.json').read_text());summary['arms'][arm]['terminal']={k:data.get(k)for k in ['elapsed_seconds','assessment_status','stop_reason','infrastructure_error','research_stage_submitted']}
  with (D/'observation/RESOURCE_OBSERVATIONS.jsonl').open('a')as f:f.write(json.dumps(s)+'\n')
 if time.monotonic()-last_disk>=60:last_disk=time.monotonic()
 summary['last_utc']=now();atomic(D/'observation/SUMMARY.json',summary)
 if all_terminal:break
 time.sleep(15)
