import json,subprocess,time
from pathlib import Path
D=Path('/data/ivy-rh080-next-20261125');unit='ivy-rh080-exposure-portable-source-cold-v1.service';run=D/'exposure-clean-source-cold-v1';output=D/'EXPOSURE_CLEAN_CGROUP_COMPLETION_OBSERVATION.json'
if output.exists():raise ValueError('Fresh observation receipt required')
raw=subprocess.check_output(['systemctl','--user','show',unit,'--property=ControlGroup','--value'],text=True).strip()
if not raw.startswith('/') or raw=='/' or not raw.endswith('/'+unit):raise ValueError('Actual owned cgroup unavailable; never read host root')
base=Path('/sys/fs/cgroup')/raw.lstrip('/')
def snapshot():
 try:return dict(monotonic=time.monotonic(),path=raw,memory_events=(base/'memory.events').read_text(),memory_current=(base/'memory.current').read_text())
 except FileNotFoundError:return None
first=snapshot();last=first;completed=None;started=time.monotonic()
while time.monotonic()-started<600:
 s=snapshot()
 if s:last=s
 if(run/'RESULT.json').is_file():
  completed=s;break
 if s is None:break
 time.sleep(.01)
record=dict(status='OWNED_CGROUP_COMPLETION_OBSERVATION',unit=unit,path=raw,first_observed=first,last_observed=last,completed_result_exists=(run/'RESULT.json').is_file(),at_completed_result=completed,final_OOM_counters_available=completed is not None,initial_unit_creation_counters_not_captured=True)
if completed:
 events={k:int(v)for k,v in(l.split()for l in completed['memory_events'].splitlines())};record['actual_completed_absolute_OOM_counters']={k:events.get(k)for k in['oom','oom_kill','oom_group_kill']}
with output.open('x')as f:json.dump(record,f,indent=2);f.write('\n')
print(record['status'],record['final_OOM_counters_available'])
