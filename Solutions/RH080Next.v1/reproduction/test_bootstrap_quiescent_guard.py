#!/usr/bin/env python3
"""Actual owned renaming-process resource controls; no proof/PV claim."""
from pathlib import Path
import argparse,json,os,signal,subprocess,sys,time
import bootstrap_quiescent_resource_guard as g

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def write(p,j):p.write_text(json.dumps(j,indent=2)+'\n')
WORKER="""from pathlib import Path
import argparse,os,subprocess,sys,time,json
p=argparse.ArgumentParser();p.add_argument('--dir',type=Path,required=True);p.add_argument('--seconds',type=float,default=3);p.add_argument('--spawn',action='store_true');p.add_argument('--exit-code',type=int,default=0);a=p.parse_args();a.dir.mkdir(parents=True,exist_ok=True)
child=None
if a.spawn:child=subprocess.Popen([sys.executable,__file__,'--dir',str(a.dir/'nested'),'--seconds',str(a.seconds)],start_new_session=True)
end=time.monotonic()+a.seconds;count=0
while time.monotonic()<end:
 temporary=a.dir/(str(count%32)+'.part');target=a.dir/(str(count%32)+'.ltar');temporary.write_bytes(b'x'*8192);os.replace(temporary,target);target.unlink();count+=1
if child is not None:child.wait()
(a.dir/'DONE.json').write_text(json.dumps({'renames':count,'PID':os.getpid(),'code':a.exit_code}))
sys.exit(a.exit_code)
"""
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args();need(not a.out.exists(),'Fresh controls directory required');a.out.mkdir(parents=True)
 old=g.original();before=old.cgroup();cg=Path(before['path']);relative='/'+str(cg.relative_to('/sys/fs/cgroup'))
 need(before.get('memory.max')==str(300*2**30)and before.get('memory.swap.max')=='0','Owned300GiB/noSwap test service required')
 worker=a.out/'rename_worker.py';worker.write_text(WORKER);records=[];source=Path(g.__file__)
 for mode,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
  root=a.out/label;root.mkdir();workspace=root/'workspace';workspace.mkdir();receipt=root/'RESOURCE.json'
  command=[sys.executable,str(worker),'--dir',str(workspace/'producer'),'--seconds','3','--spawn'];manifest=dict(command=command,source_pins=[dict(path=str(worker),sha256=g.sha(worker))]);plan=root/'command.json';write(plan,manifest)
  cmd=[sys.executable,*mode,str(source),'--root',str(root),'--workspace',str(workspace),'--command',str(plan),'--receipt',str(receipt),'--live',str(root/'LIVE.json'),'--deadline-seconds','30','--sample-seconds','.05']
  bystander=subprocess.Popen([sys.executable,'-c','import time;time.sleep(60)']);begin=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
  sibling=g.process(bystander.pid,relative);need(sibling is not None and sibling['state']not in ['T','t'],'Unrelated sibling was stopped');bystander.terminate();bystander.wait()
  (root/'guard.stdout').write_text(r.stdout);(root/'guard.stderr').write_text(r.stderr);need(r.returncode==0,'Actual renaming guard rejected: '+r.stderr[-500:])
  result=g.read(receipt);need(result['status']=='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'and result['returncode']==0,'Missing guard completion')
  need(result['samples']and all(row['complete_scan_returncode']==0 for row in result['samples']),'Incomplete scan accepted')
  for observation in result['paused_scan_observations']:
   alive=[p for p in observation['stable_stopped']if p['state']not in ['Z','X']]
   need(all(p['state']in ['T','t']and p['UID']==os.getuid()and p['cgroup']==relative for p in alive),'Unverified stopped identity')
   need({p['PID']for p in alive}<=set(observation['resumed_PIDs']),'Stopped process missing finally resume')
  for name in ['producer','producer/nested']:need(g.read(workspace/name/'DONE.json')['renames']>0,'No actual renaming work')
  records.append(dict(mode=label,case='actual-renaming-nested-session-sibling-protection',command=cmd,returncode=r.returncode,seconds=time.monotonic()-begin,receipt_sha256=g.sha(receipt),paused_scans=len(result['samples'])))
  child=subprocess.Popen([sys.executable,str(worker),'--dir',str(root/'exception-producer'),'--seconds','3'],start_new_session=True);info=g.process(child.pid,relative);need(info is not None,'Exception worker absent');failed=False
  try:
   def rejected_scan():return old.disk_scan(root/'intentionally-absent')
   g.paused_scan(g.identity(info),cg,relative,rejected_scan)
  except RuntimeError as error:failed='No complete disk scan after five attempts'in str(error)
  need(failed,'Five failed scans were accepted');deadline=time.monotonic()+1
  while time.monotonic()<deadline:
   info=g.process(child.pid,relative)
   if info is None or info['state']not in ['T','t']:break
   time.sleep(.01)
  need(info is None or info['state']not in ['T','t'],'Exception left worker stopped');child.wait(timeout=5)
  records.append(dict(mode=label,case='five-failed-scans-rejected-worker-resumed',accepted=False,worker_exitcode=child.returncode))
  calls=[]
  def runner(argv,**kwargs):
   calls.append(argv)
   if len(calls)==1:return subprocess.CompletedProcess(argv,1,'9999999999 partial\n','synthetic nonzero observation')
   return subprocess.run(argv,**kwargs)
  actual,retries=old.disk_scan(root,runner=runner);expected,_=old.disk_scan(root)
  need(actual==expected and len(retries)==1 and len(calls)==2,'Partial scan influenced acceptance');records.append(dict(mode=label,case='nonzero-partial-never-used',rejected_observations=1,returned_complete_value=actual))
  failwork=root/'failure-work';failwork.mkdir();failplan=root/'failure-command.json';write(failplan,dict(command=[sys.executable,str(worker),'--dir',str(failwork/'producer'),'--seconds','.3','--exit-code','7'],source_pins=manifest['source_pins']))
  failreceipt=root/'FAILED_RESOURCE.json';fcmd=[sys.executable,*mode,str(source),'--root',str(root),'--workspace',str(failwork),'--command',str(failplan),'--receipt',str(failreceipt),'--live',str(root/'FAILED_LIVE.json'),'--deadline-seconds','10','--sample-seconds','.05'];bad=subprocess.run(fcmd,capture_output=True,text=True)
  need(bad.returncode!=0,'Failed child accepted');fr=g.read(failreceipt);need(fr['returncode']==7 and fr['status']=='INCOMPLETE_NO_BOOTSTRAP_RESOURCE_ACCEPTANCE','Child failure promoted');records.append(dict(mode=label,case='actual-child-exit7-rejected',command=fcmd,returncode=bad.returncode,receipt_sha256=g.sha(failreceipt)))
  # A real guard interruption must resume and stop its owned nested lineage.
  stopwork=root/'stop-work';stopwork.mkdir();stopplan=root/'stop-command.json';write(stopplan,dict(command=[sys.executable,str(worker),'--dir',str(stopwork/'producer'),'--seconds','30','--spawn'],source_pins=manifest['source_pins']))
  stopreceipt=root/'STOPPED_RESOURCE.json';live=root/'STOPPED_LIVE.json';scmd=[sys.executable,*mode,str(source),'--root',str(root),'--workspace',str(stopwork),'--command',str(stopplan),'--receipt',str(stopreceipt),'--live',str(live),'--deadline-seconds','30','--sample-seconds','.05']
  stopped=subprocess.Popen(scmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True);until=time.monotonic()+10
  while not live.exists()and stopped.poll()is None and time.monotonic()<until:time.sleep(.01)
  need(live.exists(),'Stop control did not reach actual scan');os.kill(stopped.pid,signal.SIGTERM);stopout,stoperr=stopped.communicate(timeout=10)
  need(stopped.returncode!=0 and stopreceipt.exists(),'Interrupted guard accepted or lost receipt');sr=g.read(stopreceipt);need(sr['status']=='INCOMPLETE_NO_BOOTSTRAP_RESOURCE_ACCEPTANCE'and 'InterruptedError'in(sr['failure']or''),'Interruption not recorded')
  for observation in sr['paused_scan_observations']:
   for oldprocess in observation['stable_stopped']:
    now=g.process(oldprocess['PID'],relative)
    need(now is None or g.identity(now)!=g.identity(oldprocess)or now['state']in ['Z','X'],'Interrupted child remained live/stopped')
  records.append(dict(mode=label,case='actual-SIGTERM-owned-lineage-clean-stop',command=scmd,returncode=stopped.returncode,receipt_sha256=g.sha(stopreceipt)))
 write(a.out/'RESULT.json',dict(status='PASS_ACTUAL_QUIESCENT_RENAMING_RESOURCE_CONTROLS_ALL_PYTHON_MODES',records=records,source_files={p.name:g.sha(p)for p in [source,Path(__file__),g.ORIGINAL]},actual_owned_service=before['path'],resource_guard_only_not_mathematical_or_PV_acceptance=True,production_fetch_executed=False,partial_scans_never_accepted=True,unrelated_sibling_never_signalled=True));print('PASS actual quiescent renaming controls all3Python modes')
if __name__=='__main__':main()
