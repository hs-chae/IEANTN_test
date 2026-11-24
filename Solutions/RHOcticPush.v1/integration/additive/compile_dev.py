#!/usr/bin/env python3
"""Development of the actual two-moment canonical provider; not final replay."""
from pathlib import Path
import json,os,subprocess,time,resource,hashlib,argparse
R=Path(__file__).resolve().parents[4];H=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve()
if out.exists():raise ValueError('fresh output required')
obj=out/'objects';obj.mkdir(parents=True);logs=out/'logs';logs.mkdir()
banks=[Path('/data/ivy-rh-octic-20261123/box/first-moment-provider-dev-union'),Path('/data/ivy-rh-octic-20261123/box-second-moment-v1/objects'),R/'.lake/build/lib/lean']
for bank in banks:
 for f in bank.rglob('*.olean'):
  q=obj/f.relative_to(bank)
  if q.exists()or q.is_symlink():continue
  q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(f.resolve())
ctx=json.loads((R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text());env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[obj,*ctx['generic_libraries']]))
rows=[('IEANTN.Nodes.BoxMellinInputs.v2.Conclusions',R/'IEANTN/Nodes/BoxMellinInputs/v2/Conclusions.lean'),('BoxMomentNode',H/'BoxMomentNode.lean'),('BoxMomentEvolution',H/'BoxMomentEvolution.lean')];records=[]
for mod,src in rows:
 q=obj/(mod.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if q.is_symlink():q.unlink()
 cmd=[ctx['compiler'],'--root='+str(R if mod.startswith('IEANTN.')else H),'-j2','-o',str(q),str(src)];t=time.monotonic();cp=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=R,env=env,capture_output=True,text=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(64<<30,64<<30)));(logs/(mod+'.stdout')).write_text(cp.stdout);(logs/(mod+'.stderr')).write_text(cp.stderr);records.append({'module':mod,'source':str(src.relative_to(R)),'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'returncode':cp.returncode,'seconds':time.monotonic()-t});(out/'BUILD.json').write_text(json.dumps({'development_only':True,'rows':records},indent=2)+'\n');print(mod,cp.returncode,flush=True)
 if cp.returncode:print(cp.stdout[-3000:]);raise SystemExit(cp.returncode)
(out/'RESULT.json').write_text(json.dumps({'status':'PASS_DEV_ONLY','rows':records},indent=2)+'\n')
