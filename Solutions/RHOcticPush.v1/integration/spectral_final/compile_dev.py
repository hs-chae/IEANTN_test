#!/usr/bin/env python3
from pathlib import Path
import json,os,hashlib,subprocess,time,resource,argparse
H=Path(__file__).resolve().parent;I=H.parent;S=I.parent;R=S.parents[1]
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();o=a.out.resolve()
if o.exists():raise ValueError('fresh DEV namespace')
obj=o/'objects';obj.mkdir(parents=True);logs=o/'logs';logs.mkdir();banks=[Path('/data/ivy-rh-octic-20261123/integration/closed-box33-v1/union')]
for q in json.loads((S/'spectral-076/SOURCE_FREEZE.json').read_text())['modules']:
 if hashlib.sha256((R/q['path']).read_bytes()).hexdigest()!=q['sha256']:raise ValueError(q['module'])
 banks.append(Path(q['developer_bank']))
for b in banks:
 for f in b.rglob('*.olean'):
  q=obj/f.relative_to(b)
  if q.exists()or q.is_symlink():continue
  q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(f.resolve())
c=json.loads((R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text());env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[obj,*c['generic_libraries']]))
rows=[('IEANTN.Nodes.RHPrimeCounting.v5.Conclusions',R/'IEANTN/Nodes/RHPrimeCounting/v5/Conclusions.lean'),('SpectralNetwork',H/'SpectralNetwork.lean')];done=[]
for mod,src in rows:
 q=obj/(mod.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if q.is_symlink():q.unlink()
 cmd=[c['compiler'],'--root='+str(R if mod.startswith('IEANTN.')else H),'-j2','-o',str(q),str(src)];t=time.monotonic();p=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=R,env=env,capture_output=True,text=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(64<<30,64<<30)));(logs/(mod+'.stdout')).write_text(p.stdout);(logs/(mod+'.stderr')).write_text(p.stderr);done.append({'module':mod,'source':str(src.relative_to(R)),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'command':cmd,'returncode':p.returncode,'seconds':time.monotonic()-t});(o/'BUILD.json').write_text(json.dumps({'status':'PASS_DEV_ONLY'if p.returncode==0 else'FAIL_DEV','rows':done},indent=2)+'\n');print(mod,p.returncode,flush=True)
 if p.returncode:print(p.stdout[-4500:]);raise SystemExit(p.returncode)
(o/'RESULT.json').write_text(json.dumps({'status':'PASS_DEV_ONLY','rows':done},indent=2)+'\n')
