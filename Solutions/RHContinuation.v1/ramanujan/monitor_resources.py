#!/usr/bin/env python3
"""Record actual owned user-service cgroup counters while it exists."""
from pathlib import Path
import argparse,subprocess,time,json,os,datetime
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--unit',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise ValueError('fresh output required')
rows=[];peak=0;events={};beg=time.monotonic()
while True:
 r=subprocess.run(['systemctl','--user','show',a.unit,'-p','ActiveState','-p','ControlGroup','-p','MainPID','-p','CPUUsageNSec'],capture_output=True,text=True);v=dict(s.split('=',1)for s in r.stdout.splitlines()if'='in s);cg=Path('/sys/fs/cgroup')/v.get('ControlGroup','').lstrip('/')
 if v.get('ActiveState')!='active' or not v.get('ControlGroup'):break
 q={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'systemd':v}
 for n in ['memory.current','memory.peak','memory.events','memory.max','cpu.stat']:
  try:q[n]=(cg/n).read_text().strip()
  except FileNotFoundError:pass
 for n in ['memory.current','memory.peak']:
  if q.get(n,'').isdigit():peak=max(peak,int(q[n]))
 for line in q.get('memory.events','').splitlines():
  k,z=line.split();events[k]=max(events.get(k,0),int(z))
 rows.append(q);time.sleep(1)
j={'status':'COMPLETE_OWNED_CGROUP_MONITOR','unit':a.unit,'seconds_observed':time.monotonic()-beg,'samples':len(rows),'observed_cgroup_memory_peak_bytes':peak,'memory_events_max':events,'started_after_job_launch':True,'first':rows[0]if rows else None,'last':rows[-1]if rows else None,'note':'memory.peak retains earlier peak from the current unit; max is actual cgroup value. Monitor start is later than launch; execution receipts measure full command time.'};a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.pending');tmp.write_text(json.dumps(j,indent=2)+'\n');os.replace(tmp,a.out);print(json.dumps({k:j[k]for k in['status','samples','observed_cgroup_memory_peak_bytes','memory_events_max']}))
