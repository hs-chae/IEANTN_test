from pathlib import Path
import os,signal,time,json,hashlib
D=Path(__file__).resolve().parent;req=json.loads((D/'DRAIN_REQUEST.json').read_text());driver=req['processes'][0];children=req['processes'][1:]
def actual(r):
 p=Path('/proc')/str(r['pid'])
 try:
  f=(p/'stat').read_text().rsplit(')',1)[1].split()
  if int(f[19])!=r['startticks']:return None
  return f
 except FileNotFoundError:return None
observed=[]
for r in children:
 while True:
  f=actual(r)
  if f is None:observed.append({**r,'drained':True,'exit_status':'unavailable after natural exit'});break
  if f[0]=='Z':
   status=int(f[49]) if len(f)>49 else None
   observed.append({**r,'drained':True,'exit_wait_status':status,'returncode':os.waitstatus_to_exitcode(status)if status is not None else None});break
  time.sleep(1)
f=actual(driver)
if f is not None:
 os.kill(driver['pid'],signal.SIGTERM);os.kill(driver['pid'],signal.SIGCONT)
 for _ in range(10):
  f=actual(driver)
  if f is None or f[0]=='Z':break
  time.sleep(.2)
 f=actual(driver)
 if f is not None and f[0]!='Z':raise RuntimeError('owned stopped driver did not terminate')
rows=[]
for stderr in sorted(D.glob('*.stderr')):
 stdout=stderr.with_suffix('.stdout')
 if stdout.is_file():rows.append({'case':stderr.stem,'stdout_sha256':hashlib.sha256(stdout.read_bytes()).hexdigest(),'stderr_sha256':hashlib.sha256(stderr.read_bytes()).hexdigest()})
receipt={'status':'INTERRUPTED_BY_USAGE_GUARD_PARTIAL_NOT_PASS','completed_recorded_log_pairs':len(rows),'required_full_decisions':36,'recorded_logs':rows,'last_invocations':observed,'driver_pid':driver['pid'],'driver_startticks':driver['startticks'],'driver_terminated_after_current_invocation':True,'atomic_PASS_RESULT_present':(D/'RESULT.json').exists(),'ended_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'restart':'Preserve this partial run; rerun the frozen test script against accepted feedback-fresh4-v1 into a new sibling output directory. No source/math/fresh718 result changed. The final drained invocation was not collected by the stopped parent and is not counted among completed log decisions.'}
(D/'PARTIAL_STOP.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
