#!/usr/bin/env python3
"""Additive bounded-workspace resource guard with complete scans of paused owned workers.
Not a mathematical checker/PV result. Frozen production supervisors are unchanged.
"""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,os,signal,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
ORIGINAL=HERE.parent/'pv/supervise_resource_run.py'
ORIGINAL_SHA='03015a743b49c1cb840e2cb5e2a6c6d7e49be93b69aa244cf6f698b7dff74d56'
GiB=2**30

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pairs(items):
 result={}
 for k,v in items:need(k not in result,'Duplicate JSON key');result[k]=v
 return result
def read(p):return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError('Nonfinite JSON')))
def original():
 need(sha(ORIGINAL)==ORIGINAL_SHA,'Frozen original resource helper changed')
 spec=importlib.util.spec_from_file_location('original_resource_guard',ORIGINAL);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def process(pid,cgroup_path):
 p=Path('/proc')/str(pid)
 try:
  uid=p.stat().st_uid;raw=(p/'stat').read_text();fields=raw[raw.rfind(')')+2:].split();membership=(p/'cgroup').read_text()
 except(FileNotFoundError,ProcessLookupError):return None
 if uid!=os.getuid()or '0::'+cgroup_path+'\n'not in membership:return None
 return dict(PID=pid,start_ticks=int(fields[19]),PPID=int(fields[1]),state=fields[0],UID=uid,cgroup=cgroup_path)
def identity(p):return(p['PID'],p['start_ticks'],p['UID'],p['cgroup'])
def snapshot(cg,cgroup_path):
 rows={}
 for value in (cg/'cgroup.procs').read_text().split():
  p=process(int(value),cgroup_path)
  if p is not None:rows[p['PID']]=p
 return rows

def descendants(root_identity,cg,cgroup_path):
 rows=snapshot(cg,cgroup_path);root=rows.get(root_identity[0]);result={}
 if root is None:return result
 need(identity(root)==root_identity,'Fetch root PID identity changed')
 result[root['PID']]=root
 changed=True
 while changed:
  changed=False
  for pid,p in rows.items():
   if pid not in result and p['PPID']in result:result[pid]=p;changed=True
 return result

def signal_exact(p,sig):
 now=process(p['PID'],p['cgroup'])
 if now is None:return None
 need(identity(now)==identity(p),'PID identity changed before signal')
 fd=os.pidfd_open(p['PID'],0)
 again=process(p['PID'],p['cgroup'])
 if again is None:os.close(fd);return None
 need(identity(again)==identity(p),'PID identity changed during pidfd capture')
 try:signal.pidfd_send_signal(fd,sig,None,0)
 except ProcessLookupError:os.close(fd);return None
 return fd

def paused_scan(root_identity,cg,cgroup_path,scan,timeout=10):
 paused={};stable=None;observations=[];resumed=[];resume_errors=[];start=time.monotonic()
 try:
  while True:
   rows=descendants(root_identity,cg,cgroup_path)
   for p in rows.values():
    key=identity(p)
    if key not in paused and p['state']not in ['Z','X']:
     need(p['state']not in ['T','t'],'Child was already stopped outside this guard')
     fd=signal_exact(p,signal.SIGSTOP)
     if fd is not None:paused[key]=(fd,p)
   current=descendants(root_identity,cg,cgroup_path)
   keys={identity(p)for p in current.values()if p['state']not in ['Z','X']}
   stopped=all(p['state']in ['T','t','Z','X']for p in current.values())
   if stopped and keys==stable:
    observations=[dict(p)for p in current.values()];break
   stable=keys if stopped else None
   need(time.monotonic()-start<timeout,'Owned fetch lineage did not reach stable stopped state')
   time.sleep(.02)
  # Only fully successful original disk_scan results can return from scan().
  return scan(),dict(stable_stopped=observations,resumed_PIDs=resumed,resume_errors=resume_errors,seconds=time.monotonic()-start)
 finally:
  mask=signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGTERM,signal.SIGINT})
  for key,(fd,p)in reversed(list(paused.items())):
   try:
    signal.pidfd_send_signal(fd,signal.SIGCONT,None,0);resumed.append(p['PID'])
   except ProcessLookupError:pass
   except OSError as error:resume_errors.append(dict(PID=p['PID'],error=str(error)))
   finally:os.close(fd)
  signal.pthread_sigmask(signal.SIG_SETMASK,mask)
  need(not resume_errors,'Owned child resume errors: '+str(resume_errors))

def terminate_lineage(root_identity,cg,cgroup_path,known=None):
 targets={}if known is None else dict(known)
 targets.update(descendants(root_identity,cg,cgroup_path))
 for sig,delay in [(signal.SIGCONT,.05),(signal.SIGTERM,2),(signal.SIGKILL,.1)]:
  targets.update(descendants(root_identity,cg,cgroup_path))
  for p in reversed(list(targets.values())):
   try:
    fd=signal_exact(p,sig)
    if fd is not None:os.close(fd)
   except ProcessLookupError:pass
  time.sleep(delay)

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False)
 for name in ['root','workspace','command','receipt','live']:ap.add_argument('--'+name,required=True,type=Path)
 ap.add_argument('--deadline-seconds',type=int,default=1200);ap.add_argument('--sample-seconds',type=float,default=5)
 ap.add_argument('--workspace-limit-gib',type=int,default=24)
 ap.add_argument('--initial-scratch-limit-gib',type=int,default=270)
 a=ap.parse_args();need(1<=a.workspace_limit_gib<=24,'Workspace cap must be an integer1..24GiB');workspace_limit=a.workspace_limit_gib*GiB
 need(1<=a.initial_scratch_limit_gib<=280,'Initial campaign cap must be an integer1..280GiB')
 need(0<a.deadline_seconds<=1200 and .02<=a.sample_seconds<=30,'Bounded deadline/sample interval required')
 need(not a.receipt.exists(),'Fresh resource receipt required');need(a.workspace.resolve().is_relative_to(a.root.resolve()),'Workspace must be under whole owned campaign root')
 need(hasattr(os,'pidfd_open')and hasattr(signal,'pidfd_send_signal'),'Linux pidfd process identity support required')
 old=original();plan=read(a.command);cmd=plan['command'];need(type(cmd)is list and cmd and all(type(v)is str and v for v in cmd),'Concrete argv required')
 need(len({row['path']for row in plan['source_pins']})==len(plan['source_pins']),'Duplicate source pin')
 for row in plan['source_pins']:need(sha(Path(row['path']))==row['sha256'],'Pinned execution source changed')
 before=old.cgroup();need(before.get('memory.max')==str(300*GiB)and before.get('memory.swap.max')=='0','Owned physical300GiB/noSwap required')
 cg=Path(before['path']);relative='/'+str(cg.relative_to('/sys/fs/cgroup'));need(relative.endswith('.service'),'Owned service required')
 initial,retries=old.disk_scan(a.root);ram=old.available();v=os.statvfs(a.root);free=v.f_bavail*v.f_frsize
 need(ram>=2**40 and free>=2**40 and initial<a.initial_scratch_limit_gib*GiB,'Separate fresh RAM/disk/campaign admission failed')
 need(initial+workspace_limit<288*GiB,'Selected bounded workspace plus2GiBFinalreserve does not fit current owned storage')
 started=time.monotonic();child=None;root_identity=None;failure=None;code=None;samples=[];observations=[];known={}
 def interrupted(sig,frame):raise InterruptedError('Quiescent bootstrap guard received signal '+str(sig))
 for sig in [signal.SIGTERM,signal.SIGINT]:signal.signal(sig,interrupted)
 try:
  out=a.receipt.with_suffix('.stdout');err=a.receipt.with_suffix('.stderr')
  with out.open('xb')as stdout,err.open('xb')as stderr:
   child=subprocess.Popen(cmd,stdout=stdout,stderr=stderr,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),start_new_session=True)
   p=process(child.pid,relative)
   if p is not None:root_identity=identity(p)
   while child.poll()is None:
    need(root_identity is not None,'Live child identity unavailable')
    def scan():
     whole,whole_retry=old.disk_scan(a.root)
     workspace,work_retry=old.disk_scan(a.workspace)if a.workspace.exists()else(0,[])
     return dict(whole_campaign_bytes=whole,workspace_bytes=workspace,whole_scan_retries=whole_retry,workspace_scan_retries=work_retry,complete_scan_returncode=0)
    disk,stopped=paused_scan(root_identity,cg,relative,scan)
    known.update({p['PID']:p for p in stopped['stable_stopped']})
    row=dict(seconds=time.monotonic()-started,**disk,cgroup=old.cgroup(),available_RAM_bytes=old.available());samples.append(row);observations.append(stopped)
    temp=a.live.with_suffix('.pending');temp.write_text(json.dumps(row,indent=2)+'\n');os.replace(temp,a.live)
    need(row['whole_campaign_bytes']<288*GiB and row['workspace_bytes']<workspace_limit,'Whole288GiB/selected bounded workspace guard reached')
    need(row['available_RAM_bytes']>=256*GiB,'Host256GiBreserve reached')
    need(time.monotonic()-started<a.deadline_seconds,'Bounded bootstrap wall deadline reached')
    time.sleep(a.sample_seconds)
   code=child.wait()
 except BaseException as error:failure=type(error).__name__+': '+str(error)
 finally:
  signal.pthread_sigmask(signal.SIG_BLOCK,{signal.SIGTERM,signal.SIGINT})
  if child is not None and child.poll()is None and root_identity is not None:terminate_lineage(root_identity,cg,relative,known)
  if child is not None:
   try:code=child.wait(timeout=5)
   except subprocess.TimeoutExpired:failure=(failure or'')+'; child did not terminate'
  try:final=old.cgroup()
  except BaseException as error:final=dict(unavailable=type(error).__name__+': '+str(error))
  result=dict(status='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'if code==0 and failure is None else'INCOMPLETE_NO_BOOTSTRAP_RESOURCE_ACCEPTANCE',returncode=code,failure=failure,seconds=time.monotonic()-started,command=cmd,command_file_sha256=sha(a.command),guard_sha256=sha(Path(__file__)),original_helper_sha256=ORIGINAL_SHA,before=before,final=final,samples=samples,paused_scan_observations=observations,admission=dict(available_RAM_bytes=ram,free_disk_bytes=free,owned_scratch_bytes=initial,disk_scan_retries=retries,workspace_limit_bytes=workspace_limit,workspace_limit_gib=a.workspace_limit_gib,initial_campaign_limit_gib=a.initial_scratch_limit_gib),sampled_disk_and_memory_not_exact_instant_peak=True,only_owned_child_lineage_paused=True,always_resume_in_finally=True,mathematical_or_PV_acceptance=False)
  old.publish(a.receipt,result)
 need(result['status']=='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE',failure or'Child unsuccessful')
 print('PASS owned bootstrap resource accounting only; no mathematical/PV acceptance')
if __name__=='__main__':main()
