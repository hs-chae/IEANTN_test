#!/usr/bin/env python3
"""Development compile only; final fresh source closure is a separate gate."""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,time,resource,re
r=Path(__file__).resolve().parents[3]
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--source',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--bank',type=Path,action='append',default=[]);a=p.parse_args()
if a.out.exists():raise SystemExit('Fresh output required')
a.out.mkdir(parents=True);(a.out/'objects').mkdir()
c=json.loads((r/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json').read_text());source=a.source.resolve();before=hashlib.sha256(source.read_bytes()).hexdigest()
banks=[*a.bank,r/'.lake/build/lib/lean'];env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[a.out/'objects',*banks,*c['generic_libraries']]))
cmd=[c['compiler'],'--root='+str(source.parent),'-j2','-o',str(a.out/'objects'/(source.stem+'.olean')),str(source)]
def limits():resource.setrlimit(resource.RLIMIT_AS,(64<<30,64<<30))
start=time.monotonic();cp=subprocess.run(['/usr/bin/time','-v',*cmd],env=env,cwd=source.parent,capture_output=True,text=True,preexec_fn=limits)
(a.out/'stdout').write_text(cp.stdout);(a.out/'stderr').write_text(cp.stderr)
if hashlib.sha256(source.read_bytes()).hexdigest()!=before:raise SystemExit('Source changed during compile')
rows=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",cp.stdout,re.S)
standard={'propext','Classical.choice','Quot.sound'}
if cp.returncode==0 and any({x.strip() for x in ax.split(',') if x.strip()}-standard for _,ax in rows):raise SystemExit('Nonstandard axiom')
receipt={'status':'PASS_DEV' if cp.returncode==0 else 'FAIL_DEV','source':str(source.relative_to(r)),'source_sha256':before,'cmd':cmd,'banks':list(map(str,banks)),'development_only':True,'returncode':cp.returncode,'wall_seconds':time.monotonic()-start,'axioms':[{'name':n,'axioms':ax}for n,ax in rows]}
(a.out/'RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));print(cp.stdout[-10000:] if cp.returncode else '')
raise SystemExit(cp.returncode)
