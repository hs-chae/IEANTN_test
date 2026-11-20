#!/usr/bin/env python3
"""Start independent observer BEFORE the approved controller; never approves a plan."""
from pathlib import Path
import argparse,hashlib,json,os,signal,subprocess,sys,time
from monitor_demand_resources import identity,need
from execute_demand_high_resource import strict_text
S=Path(__file__).resolve().parents[1]
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--command-json',type=Path,required=True);p.add_argument('--controller-sha256',required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--path',type=Path,action='append',required=True);p.add_argument('--control',action='store_true');a=p.parse_args();c=strict_text((S/'BUILD_CONTEXT.json').read_text());owned=Path(c['new_application_object_root']).resolve().parent;out=a.out.resolve();command=strict_text(a.command_json.read_text());controller=S/'scripts/execute_demand_high_resource.py';observer=S/'scripts/observe_high_campaign.py'
 need(isinstance(command,list)and all(isinstance(v,str)for v in command)and len(command)>2 and Path(command[0]).resolve()==Path(sys.executable).resolve(),'exact interpreter and argument vector');offset=1 if command[1]not in ['-O','-OO']else 2;need(Path(command[offset]).resolve()==controller.resolve()and sha(controller)==a.controller_sha256,'reviewed exact controller bytes');need(('--control'in command)==a.control,'explicit control/research mode');need(a.control or '--approved-plan'in command,'research already requires independently approved plan');need(out.is_relative_to(owned)and not out.exists(),'fresh owned observation launch');out.mkdir(parents=True);ready=out/'OBSERVER_READY.json';stop=out/'OBSERVER_STOP.json';child=None;stop_requested=[]
 def drain(sig,frame):
  stop_requested.append(signal.Signals(sig).name)
  if child is not None and child.poll()is None:os.kill(child.pid,signal.SIGUSR1)
 for sig in [signal.SIGINT,signal.SIGTERM,signal.SIGUSR1]:signal.signal(sig,drain)
 observe=[sys.executable]+(['-OO']if sys.flags.optimize>=2 else['-O']if sys.flags.optimize else[])+[str(observer),'--pid',str(os.getpid()),'--out',str(out/'observer'),'--ready-file',str(ready),'--stop-file',str(stop),'--interval','1']
 for path in a.path:observe+=['--path',str(path)]
 started=time.monotonic()
 with(out/'observer.stdout').open('w')as so,(out/'observer.stderr').open('w')as se:watcher=subprocess.Popen(observe,stdout=so,stderr=se)
 deadline=time.monotonic()+60
 while not ready.exists()and watcher.poll()is None and time.monotonic()<deadline:time.sleep(.1)
 if not ready.exists()or watcher.poll()is not None:
  stop.write_text(json.dumps(dict(reason='PRELAUNCH_OBSERVER_NOT_READY'))+'\n');watcher.wait();raise ValueError('actual observer must be ready before controller dispatch')
 first=strict_text(ready.read_text());need(first['pid']==os.getpid()and first['start_token']==identity(os.getpid()),'observer sampled actual fixed launcher');need(not stop_requested,'drain before child launch');need(sha(controller)==a.controller_sha256,'controller stable before dispatch')
 with(out/'controller.stdout').open('w')as so,(out/'controller.stderr').open('w')as se:
  child=subprocess.Popen(command,cwd=S,stdout=so,stderr=se);launch=dict(status='APPROVED_CONTROLLER_CHILD_LAUNCHED_NOT_COMPLETED',pid=child.pid,start_token=identity(child.pid),command=command,controller_sha256=a.controller_sha256,observer_source_sha256=sha(observer),observer_ready_sha256=sha(ready),observer_ready_before_child=True,launch_unix=time.time());(out/'LAUNCH.json').write_text(json.dumps(launch,indent=2)+'\n');rc=child.wait()
 stop.write_text(json.dumps(dict(controller_pid=child.pid,controller_returncode=rc,stop_unix=time.time()))+'\n');observer_rc=watcher.wait();need(observer_rc==0 and(out/'observer/RESULT.json').is_file(),'observer completed before launcher exit');need(sha(controller)==a.controller_sha256,'controller stable throughout run');result=dict(status='OBSERVED_CONTROLLER_FINISHED_NOT_SEPARATE_PROOF_ACCEPTANCE',controller_returncode=rc,observer_returncode=observer_rc,elapsed_seconds=time.monotonic()-started,observer_result_sha256=sha(out/'observer/RESULT.json'),launch_sha256=sha(out/'LAUNCH.json'),controller_source_sha256=sha(controller),wrapper_source_sha256=sha(__file__),stop_requests=stop_requested);(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));raise SystemExit(rc)
if __name__=='__main__':main()
