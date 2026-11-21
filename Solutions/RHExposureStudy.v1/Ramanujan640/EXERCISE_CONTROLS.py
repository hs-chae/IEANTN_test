#!/usr/bin/env python3
"""Actual portable validator positive/negative controls in all Python modes."""
from pathlib import Path
import argparse, copy, datetime, hashlib, json, os, signal, subprocess, sys
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--package',type=Path,required=True);p.add_argument('--replay',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();O=a.out.resolve()
if O.exists()or not O.is_relative_to(B/'validator-controls'):raise ValueError('fresh owned output required')
O.mkdir(parents=True);v=json.loads(a.replay.read_text());cases=[('actual-positive',a.replay,True)]
for i,row in enumerate(v['modules']):
    d=copy.deepcopy(v);d['modules'][i]['returncode']=1;f=O/('child-'+str(i)+'.json');f.write_text(json.dumps(d));cases.append(('child:'+row['module'],f,False))
for name,mutate in[
 ('missing-child',lambda d:d['modules'].pop(0)),
 ('probe-failure',lambda d:d['modules'][0]['compiler_dependency_probe'].update(returncode=1)),
 ('false-child-type',lambda d:d['modules'][0].update(returncode=False)),
 ('cached-application',lambda d:d.update(application_cached_objects_used=True)),
 ('bad-raw',lambda d:d.update(raw_input_sha256='0'*64)),
 ('extra-final-axiom',lambda d:d['modules'][-1].update(stdout=d['modules'][-1]['stdout'].replace('Quot.sound]','Quot.sound, sorryAx]'))),
]:
    d=copy.deepcopy(v);mutate(d);f=O/(name+'.json');f.write_text(json.dumps(d));cases.append((name,f,False))
for name,text in[('duplicate-key','{"status":0,"status":1}'),('nonfinite','{"value":NaN}')]:
    f=O/(name+'.json');f.write_text(text);cases.append((name,f,False))
result={'status':'RUNNING','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'active_module_routes':len(v['modules']),'cases':[]}
result['invocation']={'pid':os.getpid(),'parent_pid':os.getppid(),'argv':sys.argv}
def checkpoint():
    tmp=O/'PROGRESS.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(O/'PROGRESS.json')
def interrupted(signum,frame):
    result['status']='INTERRUPTED_NO_MATRIX_ACCEPTANCE';result['signal']=signum;checkpoint();raise SystemExit(128+signum)
signal.signal(signal.SIGTERM,interrupted);signal.signal(signal.SIGINT,interrupted)
checkpoint()
try:
 for name,f,expected in cases:
  for mode in[0,1,2]:
   cmd=[sys.executable]+(['-O']if mode==1 else ['-OO']if mode==2 else [])+[str(B/'validate_portable_v2.py'),'--package',str(a.package),'--replay',str(f)]
   run=subprocess.run(cmd,capture_output=True,text=True);result['cases'].append({'case':name,'optimization':mode,'returncode':run.returncode,'stdout':run.stdout,'stderr':run.stderr});checkpoint()
   if(run.returncode==0)!=expected:raise ValueError('unexpected real CLI result:'+name+':'+str(mode))
 result['status']='PASS_ALL_PORTABLE_CHILD_NEGATIVES_AND_REAL_POSITIVES_NORMAL_O_OO'
except Exception as error:result['status']='FAILED_PORTABLE_CONTROL_MATRIX';result['error']=str(error)
result['actual_cli_invocations']=len(result['cases']);result['validator_sha256']=hashlib.sha256((B/'validate_portable_v2.py').read_bytes()).hexdigest();result['replay_sha256']=hashlib.sha256(a.replay.read_bytes()).hexdigest()
tmp=O/'RESULT.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(O/'RESULT.json');print(result['status'],result['actual_cli_invocations'])
if not result['status'].startswith('PASS_'):raise SystemExit(1)
