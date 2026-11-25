#!/usr/bin/env python3
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('source',type=Path);p.add_argument('--name',required=True);p.add_argument('--objects',action='append',default=[]);a=p.parse_args();D=Path('/data/ivy-rh-080-20261125/estimates');O=D/a.name
if O.exists():raise SystemExit('Freshrunrequired')
O.mkdir();s=O/a.source.name;s.write_bytes(a.source.read_bytes());C=json.loads(Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json').read_text());env=os.environ.copy();env['LEAN_PATH']=':'.join(a.objects+[C['generic_lean_path']]);cmd=['/usr/bin/prlimit','--as=34359738368','--','/usr/bin/time','-v',C['compiler'],'-j2','--root='+str(O),'-o',str(O/(a.source.stem+'.olean')),str(s)];start=time.monotonic()
with (O/'stdout').open('wb') as out,(O/'stderr').open('wb') as err:r=subprocess.run(cmd,env=env,stdout=out,stderr=err)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();x=dict(status='PASS' if r.returncode==0 else 'FAIL',returncode=r.returncode,seconds=time.monotonic()-start,command=cmd,source_sha256=h(s),compiler_sha256=h(Path(C['compiler'])),environment={'LEAN_PATH':env['LEAN_PATH']},stdout_sha256=h(O/'stdout'),stderr_sha256=h(O/'stderr'))
(O/'RESULT.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps({k:x[k] for k in ['status','returncode','seconds']}));print((O/'stdout').read_text()[-5000:] if r.returncode else (O/'stdout').read_text()[-1200:]);raise SystemExit(r.returncode)
