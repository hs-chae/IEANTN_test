#!/usr/bin/env python3
"""Development-only compilation against explicitly pinned existing proof banks.
Final clean application closure is a separate orchestrator gate.
"""
from pathlib import Path
import argparse,hashlib,json,os,resource,subprocess,time
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('module');p.add_argument('--attempt',required=True);a=p.parse_args()
b=Path(__file__).resolve().parent;r=b.parents[2]
ctx=json.loads((r/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text())
out=Path('/data/ivy-rh-octic-20261123/analytic-octic')/a.attempt;out.mkdir(parents=True,exist_ok=False)
obj=out.parent/'objects';obj.mkdir(exist_ok=True)
source=b/(a.module+'.lean')
(out/source.name).write_bytes(source.read_bytes())
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(obj),str(r/'.lake/build/lib/lean'),'/data/ivy-rh-octic-20261123/octic-trivial-normalize-v2/objects','/data/ivy-rh-octic-20261123/octic-mellin-v4/objects','/data/ivy-rh-limit-20261122/analytic/cold113-v2/objects','/data/ivy-rh-limit-20261122/spectral/cold55-v1/objects',*ctx['generic_libraries']]);env['LEAN_NUM_THREADS']='4'
command=[ctx['compiler'],'--root='+str(b),'-j4','-o',str(obj/(a.module+'.olean')),str(source)]
start=time.monotonic();p=subprocess.run(['/usr/bin/time','-v',*command],env=env,cwd=b,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(64*1024**3,64*1024**3)))
(out/'stdout').write_text(p.stdout);(out/'stderr').write_text(p.stderr)
rec={'status':'PASS_DEVELOPMENT_REUSED_BASELINE_BANKS' if p.returncode==0 else'FAIL','command':command,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'returncode':p.returncode,'seconds':time.monotonic()-start,'LEAN_PATH':env['LEAN_PATH']}
(out/'RUN.json').write_text(json.dumps(rec,indent=2)+'\n')
print('exit',p.returncode,'seconds',round(rec['seconds'],3));print(p.stdout)
raise SystemExit(p.returncode)
