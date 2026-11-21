#!/usr/bin/env python3
"""Replay a frozen portfolio in a fresh offline namespace; no model calls."""
from pathlib import Path
import argparse,datetime,hashlib,json,os,subprocess,time
R=Path(__file__).resolve().parents[1]
D=Path('/data/ivy-rh-propagation-20261120')
HELPER=R.parent/'ieantn-exposure-maximal-20261109/sources/ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py'
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--arm',choices=['NL_RH','IEANTN_RH'],required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
O=a.out.resolve();need(O.is_relative_to(D/'post-lock-verification')and not O.exists(),'fresh study-owned destination required')
source=R/'evaluator-private/final-locks'/a.arm/'files';seal=json.loads((source.parent/'LOCKED_FINAL.json').read_text())
for row in seal['files']:need(sha(source/row['path'])==row['sha256'],'locked file changed:'+row['path'])
need(sha(HELPER)=='79c1428403befb974bf4daeada0c130addd60ff952cef4b62ca74ef18ae6d79d','namespace helper identity')
O.mkdir(parents=True);(O/'root').mkdir();(O/'work').mkdir()
specpath=D/'setup'/('preflight-'+a.arm+'-v2')/'OS_SPEC.json';spec=json.loads(specpath.read_text());spec['root']=str(O/'root')
spec['entries']=[x for x in spec['entries']if x.get('path')!='/work']+[{'kind':'rw','path':'/work','source':str(O/'work')},{'kind':'ro','path':'/replay-input','source':str(source)}]
spec['cwd']='/work'
if a.arm=='IEANTN_RH':spec['command']=['/usr/bin/python3.10','-B','/replay-input/reproduce.py','/work/reproduced']
else:spec['command']=['/bin/bash','/replay-input/verify.sh','/replay-input'];spec['env'].update(BUILD_DIR='/work/reproduced')
spec['env']['PYTHONOPTIMIZE']='0';spec['network']='offline'
(O/'OS_SPEC.json').write_text(json.dumps(spec,indent=2)+'\n')
command=['unshare','--user','--map-root-user','--mount','--propagation','private','--','/usr/bin/python3.10','-I','-B',str(HELPER),str(O/'OS_SPEC.json')]
started=time.monotonic()
with (O/'stdout').open('wb')as so,(O/'stderr').open('wb')as se:
 rc=subprocess.run(command,stdout=so,stderr=se,close_fds=True).returncode
stable=all(sha(source/r['path'])==r['sha256']for r in seal['files'])
record={'schema':'RH_FROZEN_PORTFOLIO_OFFLINE_REPLAY_V1','arm':a.arm,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS_ORIGINAL_REPRODUCER_AT_DECLARED_BOUNDARY'if rc==0 and stable else'FAILED_ORIGINAL_REPRODUCER_NO_MATH_ACCEPTANCE','returncode':rc,'elapsed_seconds':time.monotonic()-started,'source_lock_sha256':sha(source.parent/'LOCKED_FINAL.json'),'source_stable':stable,'namespace_helper_sha256':sha(HELPER),'runner_sha256':sha(__file__),'command':command,'model_calls':0,'python_optimization':0,'original_assert_checks_active':True,'no_source_first_PV_inferred':True,'new_objects_reused':False,'inherited_application_objects':'IEANTN_RH only; exact runtime manifest','stdout_sha256':sha(O/'stdout'),'stderr_sha256':sha(O/'stderr')}
tmp=O/'RESULT.pending';tmp.write_text(json.dumps(record,indent=2)+'\n');os.link(tmp,O/'RESULT.json');tmp.unlink();print(json.dumps(record,indent=2))
if rc!=0 or not stable:raise SystemExit(1)
