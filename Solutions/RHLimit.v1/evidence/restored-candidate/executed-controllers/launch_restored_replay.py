#!/usr/bin/env python3
"""Launch the approved restored packet with durable owned process/exit records."""
from pathlib import Path
import argparse,datetime,hashlib,json,subprocess,sys
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--packet',type=Path,required=True);p.add_argument('--context',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--record',type=Path,required=True);a=p.parse_args()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
packet=a.packet.resolve();context=a.context.resolve();out=a.out.resolve();record=a.record.resolve();need(not out.exists()and not record.exists(),'fresh output/launcher record required');need(json.loads((packet/'ROOT_FINAL_READY.json').read_text())['status']=='ROOT_FINAL_READY','candidate not approved')
record.mkdir(parents=True)
cmd=[sys.executable,str(packet/'run_replay_bounded.py'),'--record',str(record/'resources'),'--limit-gib','80','--group-gib','240','--wall-seconds','10800','--',sys.executable,str(packet/'REPRODUCE_RH_LIMIT.py'),'--context',str(context),'--out',str(out)]
with(record/'launcher.stdout').open('w')as so,(record/'launcher.stderr').open('w')as se:child=subprocess.Popen(cmd,stdout=so,stderr=se,start_new_session=True,cwd=record)
r={'status':'LAUNCHED_NOT_YET_COMPLETED','pid':child.pid,'command':cmd,'began_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'packet_manifest_sha256':sha(packet/'BUNDLE_MANIFEST.json'),'root_ready_sha256':sha(packet/'ROOT_FINAL_READY.json'),'orchestrator_sha256':sha(packet/'REPRODUCE_RH_LIMIT.py'),'resource_wrapper_sha256':sha(packet/'run_replay_bounded.py'),'launcher_sha256':sha(Path(__file__)),'expected_final_receipts':[str(record/'resources/RESULT.json'),str(out/'RESULT.json')]};(record/'PARENT_LAUNCH.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
