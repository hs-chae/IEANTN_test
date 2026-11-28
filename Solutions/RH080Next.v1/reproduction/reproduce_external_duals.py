#!/usr/bin/env python3
"""Plan/reproduce the four existing strongest external dual enclosures.
External directed-interval results only: no Lean/PV or network acceptance.
Default is plan-only. No random seeds or optimizer reruns are involved.
"""
from __future__ import annotations
import argparse,json,os,subprocess,sys,time
from pathlib import Path
from bootstrap_context import PROJECT,atomic,need,read_json,sha
EXPECTED=Path(__file__).with_name('EXTERNAL_DUAL_EXPECTED.json')
EXPECTED_SHA='cafa4ec1d6a625d5a68bbb25f8bdc92890ec6b3707f2443979fc6eb3e76cd248'

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False)
 ap.add_argument('--run',required=True,type=Path);ap.add_argument('--python',type=Path,default=Path(sys.executable))
 ap.add_argument('--execute',action='store_true');a=ap.parse_args()
 need(not os.path.lexists(a.run),'Fresh optional numerical replay directory required')
 need(sha(EXPECTED)==EXPECTED_SHA,'Fixed external target/source manifest differs')
 fixed=read_json(EXPECTED);interpreter=a.python.resolve(strict=True)
 query="import sys,json,importlib.metadata;print(json.dumps({'python':'.'.join(map(str,sys.version_info[:3])),'python_flint':importlib.metadata.version('python-flint')}))"
 check=subprocess.run([str(interpreter),'-c',query],capture_output=True,text=True)
 environment=json.loads(check.stdout)if check.returncode==0 else None
 available=environment==dict(python=fixed['python_version'],python_flint=fixed['python_flint_version'])
 commands=[];pins={str(EXPECTED):sha(EXPECTED),str(Path(__file__)):sha(Path(__file__))}
 for profile in fixed['profiles']:
  script=PROJECT/profile['script'];witness=PROJECT/profile['witness']
  need(sha(script)==profile['script_sha256']and sha(witness)==profile['witness_sha256'],'Fixed original numerical script/witness changed')
  pins[str(script)]=sha(script);pins[str(witness)]=sha(witness)
  command=[str(interpreter),str(script),'--witness',str(witness),'--run',str(a.run/profile['id']),'--bits',str(profile['bits'])]
  if profile['algorithm']=='DFT':command+=['--panels',str(profile['panels'])]
  command+=['--target',profile['target']];commands.append(dict(id=profile['id'],command=command,expected_status=profile['expected_result_status'],algorithm=profile['algorithm'],A=profile['A'],target=profile['target']))
 helper=PROJECT/fixed['common_helper']['file'];need(sha(helper)==fixed['common_helper']['sha256'],'Shared interval helper differs')
 a.run.mkdir(parents=True);plan=dict(status='EXTERNAL_REPLAY_EXECUTION_REQUESTED'if a.execute else'PLAN_ONLY_NOT_EXECUTED_NOT_LEAN_NOT_PV',commands=commands,source_pins=pins,interpreter=str(interpreter),interpreter_sha256=sha(interpreter),required_python=fixed['python_version'],required_python_flint=fixed['python_flint_version'],actual_environment=environment,environment_available=available,environment_query_returncode=check.returncode,source_first_PV=False,Lean_numeric_closed=False,verified_network_input=False,random_seed=None,original_trial_outcomes_changed=False)
 atomic(a.run/'PLAN.json',plan)
 if not a.execute:
  print(json.dumps(dict(status=plan['status'],profiles=len(commands),environment_available=available)));return
 need(available,'ExactPython3.12.9/python-flint0.9.0 environment required; plan preserved, no numerical run started')
 began=time.monotonic();runs=[]
 try:
  for row in commands:
   tag=row['id'];out=a.run/(tag+'.stdout');err=a.run/(tag+'.stderr');start=time.monotonic()
   with out.open('xb')as stdout,err.open('xb')as stderr:r=subprocess.run(row['command'],stdout=stdout,stderr=stderr,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
   need(r.returncode==0,'External interval verifier failed: '+tag)
   result_file=a.run/tag/'RESULT.json';result=read_json(result_file)
   need(result['status']==row['expected_status'],'Unexpected external numerical result kind: '+tag)
   if row['algorithm']=='DFT':need(result['verified_strict_upper_target']==row['target'],'External DFT target differs')
   else:need(result['target']==row['target'],'Independent Horner target differs')
   runs.append(dict(id=tag,seconds=time.monotonic()-start,returncode=r.returncode,result_sha256=sha(result_file),stdout_sha256=sha(out),stderr_sha256=sha(err)))
  for path,digest in pins.items():need(sha(Path(path))==digest,'Numerical source changed during replay')
  atomic(a.run/'RESULT.json',dict(status='PASS_FOUR_EXISTING_EXTERNAL_INTERVAL_REPLAYS_NOT_LEAN_NOT_PV',runs=runs,plan_sha256=sha(a.run/'PLAN.json'),seconds=time.monotonic()-began,source_first_PV=False,Lean_numeric_closed=False,verified_network_input=False,compiler_runtime_software_hardware_trusted=True,optimality_or_best_known_claim=False))
  print('PASS four external directed-interval replays; not Lean/PV/network approval')
 except BaseException as error:
  atomic(a.run/'FAILURE.json',dict(status='NO_EXTERNAL_REPLAY_COMPLETION',error=type(error).__name__+': '+str(error),completed=runs,seconds=time.monotonic()-began));raise
if __name__=='__main__':main()
