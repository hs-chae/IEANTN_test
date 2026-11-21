#!/usr/bin/env python3
"""Reviewed prospective pair launch using actual separate resource capacities."""
from pathlib import Path
import datetime,hashlib,json,os,shutil,subprocess,sys
R=Path(__file__).resolve().parents[1];D=Path('/data/ivy-rh-propagation-20261120');W=R.parent
PYTHON=Path('/ryu/hyunsik/PNTs/gauss/OpenGauss/venv/bin/python3')
def pin(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def write(p,d):
 if p.exists():raise RuntimeError('preserve existing launch record '+str(p))
 p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n')
def main():
 if '--check'not in sys.argv and '--execute'not in sys.argv:raise RuntimeError('specify --check or --execute')
 execute='--execute'in sys.argv
 mem={line.split(':')[0]:int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()if line.startswith(('MemAvailable:','MemTotal:'))};disk=shutil.disk_usage(D)
 if mem['MemAvailable']<512*1024**3+192*1024**3:raise RuntimeError('host reserve plus planned pair not currently safe')
 if disk.free<512*1024**3:raise RuntimeError('insufficient free disk for host reserve and research scratch')
 protocol=json.loads((R/'protocol/protocol.json').read_text());commands=[]
 if protocol['arms']!=['NL_RH','IEANTN_RH']:raise RuntimeError('exactly two arms required')
 ca=json.loads((D/'setup/SOURCE_BROKER_ALLMODE_ACCEPTANCE.json').read_text())
 if ca['status']!='PASS' or any(row['source_sha256']!=pin(R/'scripts/source_broker.py')['sha256']for row in ca['actual_cli_runs']):raise RuntimeError('current source broker actual route controls missing')
 for arm,cpus in [('NL_RH','0-7'),('IEANTN_RH','8-15')]:
  manifest=R/'protocol'/('packet-manifest-'+arm+'.json');runtime=R/'protocol'/('runtime-'+arm+'.json');preflight=D/'setup'/('preflight-'+arm+'-v2')/'PREFLIGHT.json';pf=json.loads(preflight.read_text())
  for key,path in [('controller_sha256',R/'scripts/rh_native_controller.py'),('packet_manifest_sha256',manifest),('runtime_manifest_sha256',runtime)]:
   if pf[key]!=pin(path)['sha256']:raise RuntimeError('actual preflight byte association differs '+arm+' '+key)
  if pf['status']!='PASS_EXACT_RH_PACKET_RUNTIME_OS_AND_NATIVE_TOOL_ISOLATION' or pf['model_calls']!=0:raise RuntimeError('actual preflight gate missing')
  out=D/'runs'/('primary-'+arm+'-v1');lockp=R/'protocol/locks'/('primary-'+arm+'-v1.json')
  lock={'schema':'RH_PROPAGATION_EXECUTION_LOCK_V1','status':'ROOT_APPROVED_RH_STAGE','reviewed_by':'/root','run_id':out.name,'arm':arm,'model':protocol['model'],'effort':protocol['effort'],'minimum_research_seconds':3600,'resources':{'memory_gib':96,'scratch_gib':64,'cpus':8},'packet_manifest':pin(manifest),'runtime_manifest':pin(runtime),'controller_source':pin(R/'scripts/rh_native_controller.py'),'protocol':pin(R/'protocol/protocol.json'),'preflight':pin(preflight),'source_broker':pin(R/'scripts/source_broker.py'),'source_broker_acceptance':pin(D/'setup/SOURCE_BROKER_ALLMODE_ACCEPTANCE.json'),'initial_source_ledger':pin(D/'literature'/arm/'INITIAL_SOURCE_LEDGER.json'),'coordinator_history_inherited':False,'actual_model_catalog_checked_by_controller_before_first_inference':True,'mathematical_results_predeclared':False}
  if execute:write(lockp,lock)
  cmd=[str(PYTHON),'-I','-B',str(R/'scripts/rh_native_controller.py'),'--packet-manifest',str(manifest),'--runtime',str(runtime),'--out',str(out),'--lock',str(lockp),'--model',protocol['model'],'--effort',protocol['effort'],'--initial-milestone','250000','--increment','250000','--memory-gib','96','--scratch-gib','64','--cpus','8','--minimum-research-seconds','3600']
  commands.append({'arm':arm,'cpus':cpus,'run':str(out),'lock':lock,'command':cmd,'unit':'ivy-rh-'+arm.replace('_','-').lower()+'-primary-v1'})
 if not execute:print(json.dumps({'status':'ROOT_PAIR_LAUNCH_REVIEW_READY_NO_INFERENCE','mem':mem,'disk_free':disk.free,'pair':commands},indent=2));return
 (D/'drivers').mkdir(exist_ok=True);rows=[]
 # Source broker only consumes each own-arm queue, never injects mathematical advice.
 brokerlog=(D/'drivers/source-broker.log').open('xb');broker=subprocess.Popen([str(PYTHON),'-I','-B',str(R/'scripts/source_broker.py')],stdout=brokerlog,stderr=subprocess.STDOUT,start_new_session=True);brokerlog.close()
 for row in commands:
  arm=row['arm'];env={'CODEX_HOME':os.environ.get('CODEX_HOME',str(Path.home()/'.codex')),'PATH':'/ryu/hyunsik/.nvm/versions/node/v20.20.0/bin:/usr/local/bin:/usr/bin:/bin'}
  call=['systemd-run','--user','--collect','--unit',row['unit'],'-p','MemoryMax=96G','-p','MemorySwapMax=0','-p','CPUQuota=800%','-p','StandardOutput=append:'+str(D/'drivers'/(arm+'.stdout')),'-p','StandardError=append:'+str(D/'drivers'/(arm+'.stderr')),'--working-directory='+str(W)]
  for k,v in env.items():call.extend(['--setenv',k+'='+v])
  call.extend(['/usr/bin/taskset','-c',row['cpus']]+row['command'])
  p=subprocess.run(call,capture_output=True,text=True)
  receipt={'arm':arm,'command':call,'dispatch_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'systemd_admission_exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'unit':row['unit'],'research_inference_not_inferred_from_service_admission':True};rows.append(receipt)
  write(D/'drivers'/('DISPATCH-'+arm+'.json'),receipt)
  if p.returncode:raise RuntimeError('paired service admission failed; preserve other state and repair exact failed arm')
 write(D/'drivers/PAIR_DISPATCH.json',{'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'resource_readback_before_launch':{'memory':mem,'disk_free':disk.free},'broker_pid':broker.pid,'broker_source':pin(R/'scripts/source_broker.py'),'dispatch':rows,'scientific_results':'NOT_YET_ASSESSED','simultaneous_native_first_turn_claimed':False})
 print(json.dumps({'status':'PAIRED_SERVICES_ADMITTED_ACTUAL_INFERENCE_PENDING_LIVE_CHECK','broker_pid':broker.pid,'units':[r['unit']for r in rows]}))
if __name__=='__main__':main()
