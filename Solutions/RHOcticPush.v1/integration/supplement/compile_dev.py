#!/usr/bin/env python3
"""Development only: current frozen objects reused, never final replay evidence."""
from pathlib import Path
import argparse,json,os,subprocess,time,resource,hashlib
R=Path(__file__).resolve().parents[4];I=Path(__file__).resolve().parent.parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve()
if out.exists():raise ValueError('fresh out required')
out.mkdir();obj=out/'objects';obj.mkdir();logs=out/'logs';logs.mkdir()
banks=[R/'.lake/build/lib/lean',Path('/data/ivy-rh-octic-20261123/analytic-octic/objects'),Path('/data/ivy-rh-octic-20261123/moments/endpoint/dev-union-v1'),Path('/data/ivy-rh-octic-20261123/goldbach-triples-v4/objects'),Path('/data/ivy-rh-octic-20261123/goldbach-core-v1/objects'),Path('/data/ivy-rh-octic-20261123/octic-final-source-v2/objects'),Path('/data/ivy-rh-octic-20261123/octic-optimized-certified-v1/objects')]
banks += [Path('/data/ivy-rh-octic-20261123/octic-trivial-normalize-v2/objects'),Path('/data/ivy-rh-octic-20261123/octic-mellin-v4/objects')]
for row in json.load(open(R/'Solutions/RHOcticPush.v1/moments/ANALYTIC_SOURCE_FREEZE.json'))['roots']:
 if row['status']!='PASS_DEV':raise ValueError('unaccepted analytic source')
 src=R/row['source']
 if hashlib.sha256(src.read_bytes()).hexdigest()!=row['source_sha256']:raise ValueError('analytic source drift')
 banks.append(Path(row['cmd'][row['cmd'].index('-o')+1]).parent)
for bank in banks:
 for f in bank.rglob('*.olean'):
  target=obj/f.relative_to(bank);target.parent.mkdir(parents=True,exist_ok=True)
  if target.is_symlink():target.unlink()
  if not target.exists():target.symlink_to(f.resolve())
ctx=json.load(open(R/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'));env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[obj,*ctx['generic_libraries']]))
rows=[('IEANTN.Vocabulary.GoldbachCounts',R/'IEANTN/Vocabulary/GoldbachCounts.lean')]
rows += [('IEANTN.Nodes.'+f+'.'+v+'.Conclusions',R/'IEANTN/Nodes'/f/v/'Conclusions.lean')for f,v in [('BPTOffOrdinate','v1'),('PrimeKernelInputs','v4'),('PrimeInterval','v4'),('PrimeQuantile','v3'),('Goldbach','v2')]]
rows += [('OcticVerifiedEvolution',I/'OcticVerifiedEvolution.lean')]
records=[]
for mod,src in rows:
 q=obj/(mod.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if q.is_symlink():q.unlink()
 root=R if mod.startswith('IEANTN.')else src.parent
 cmd=[ctx['compiler'],'--root='+str(root),'-j2','-o',str(q),str(src)];start=time.monotonic();cp=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=root,env=env,capture_output=True,text=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(64<<30,64<<30)));(logs/(mod+'.stdout')).write_text(cp.stdout);(logs/(mod+'.stderr')).write_text(cp.stderr);records.append({'module':mod,'source':str(src.relative_to(R)),'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'returncode':cp.returncode,'seconds':time.monotonic()-start});(out/'BUILD.json').write_text(json.dumps({'development_only':True,'records':records},indent=2)+'\n');print(mod,cp.returncode,round(time.monotonic()-start,2),flush=True)
 if cp.returncode:print(cp.stdout[-10000:]);raise SystemExit(cp.returncode)
(out/'RESULT.json').write_text(json.dumps({'status':'PASS_DEV_ONLY','records':records},indent=2)+'\n')
