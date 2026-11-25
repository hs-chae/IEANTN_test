#!/usr/bin/env python3
"""Replay the frozen predecessor source packets; no application object fallback."""
from pathlib import Path
import argparse,json,subprocess,sys,time,hashlib

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--repository',type=Path,required=True);p.add_argument('--context',type=Path,required=True);p.add_argument('--run-root',type=Path,required=True);p.add_argument('--packet',choices=['frontier300','gaussian53'],required=True);p.add_argument('--jobs',type=int,required=True);a=p.parse_args();c=json.loads(a.context.read_text());root=a.run_root.resolve()
 if root.exists():raise ValueError('Fresh run-root required')
 root.mkdir(parents=True);rel='portable' if a.packet=='frontier300' else 'gaussian_gap/portable';packet=a.repository/'Solutions/RHOnePrimeEvolution.v1'/rel
 command=[sys.executable,str(packet/'reproduce.py'),'--compiler',c['compiler'],'--generic-lean-path',c['generic_lean_path'],'--run',str(root/'run'),'--jobs',str(a.jobs)]
 receipt=dict(status='LAUNCH_NOT_ACCEPTANCE',command=command,packet=a.packet,source_manifest_sha256=hashlib.sha256((packet/'SOURCE_MANIFEST.json').read_bytes()).hexdigest(),compiler_sha256=hashlib.sha256(Path(c['compiler']).read_bytes()).hexdigest(),started_UTC=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),predecessor_application_objects_used=False)
 (root/'LAUNCH.json').write_text(json.dumps(receipt,indent=2)+'\n');start=time.monotonic()
 with (root/'stdout').open('wb') as out,(root/'stderr').open('wb') as err:result=subprocess.run(['/usr/bin/time','-v','-o',str(root/'GNU_TIME.txt')]+command,stdout=out,stderr=err)
 receipt.update(status='CONTROLLER_COMPLETED_NOT_SELF_AUTHENTICATING',returncode=result.returncode,seconds=time.monotonic()-start,completed_UTC=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
 if result.returncode==0:
  actual=json.loads((root/'run/RESULT.json').read_text());receipt['accepted_child_status']=actual['status'];receipt['child_result_sha256']=hashlib.sha256((root/'run/RESULT.json').read_bytes()).hexdigest()
 (root/'COMPLETION.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(result.returncode)
if __name__=='__main__':main()
