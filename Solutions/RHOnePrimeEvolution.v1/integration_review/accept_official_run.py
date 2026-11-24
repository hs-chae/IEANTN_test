#!/usr/bin/env python3
"""Independently check genuine bookkeeping execution and atomically publish scope.
This is not a Comparator approval or a mathematical proof receipt.
"""
import argparse,hashlib,json,os,subprocess,time
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--repository',type=Path,required=True);p.add_argument('--execution',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 R=a.repository.resolve(strict=True);execution=a.execution.resolve(strict=True);r=json.loads(execution.read_text());out=a.output.resolve()
 if out.exists():raise SystemExit('Fresh acceptance destination required')
 if r['status']!='PASS_GENUINE_LAKE_CORE_HASH_FINGERPRINT' or r['failure'] is not None:raise SystemExit('Official execution did not pass')
 if r['completed']!=373 or r['core_modules']!=373:raise SystemExit('Incorrect scoped ordinary core size')
 steps=r['subsequent'];expected=['hash-executable','fingerprint','fingerprint-check']
 if [q['name'] for q in steps]!=expected or any(q['returncode']!=0 for q in steps):raise SystemExit('Missing genuine successful commands')
 for q in steps:
  for kind in ('stdout','stderr'):
   if sha(execution.parent/'logs'/(q['name']+'.'+kind))!=q[kind+'_sha256']:raise SystemExit('Official command evidence hash mismatch')
 old=r['reused_core'];prior_path=Path(old['receipt']);prior=json.loads(prior_path.read_text());plan=json.loads((prior_path.parent/'PLAN.json').read_text())
 if sha(prior_path)!=old['sha256'] or len(prior['builds'])!=373 or any(q['returncode'] for q in prior['builds']):raise SystemExit('Invalid prior genuine core evidence')
 for q in plan['modules']:
  if sha(Path(q['file']))!=q['source_sha256']:raise SystemExit('Core source drift '+q['module'])
 for q in prior['builds']:
  for kind in ('stdout','stderr'):
   if sha(prior_path.parent/'logs'/(q['module']+'.'+kind))!=q[kind+'_sha256']:raise SystemExit('Prior core evidence hash mismatch')
 C=json.loads((R/'Solutions/RHOnePrimeEvolution.v1/scripts/LOCAL_CONTEXT.json').read_text());lake=str(Path(C['compiler']).parent/'lake');env=os.environ.copy();env['PATH']=str(Path(lake).parent)+':'+env['PATH'];env['LEAN_NUM_THREADS']='4'
 cmd=['python3','scripts/ieantn.py','fingerprint','--check'];start=time.monotonic();proc=subprocess.run(cmd,cwd=R,env=env,capture_output=True,text=True)
 if proc.returncode or proc.stdout.strip()!='ok  statement fingerprints':raise SystemExit('Fresh actual official fingerprint check failed: '+proc.stdout+proc.stderr)
 fpfiles=sorted((R/'IEANTN/Nodes').glob('*/*/fingerprints.json'))
 value=dict(status='PASS_ATOMICALLY_CHECKED_GENUINE_BOOKKEEPING',execution_receipt_sha256=sha(execution),prior_core_receipt_sha256=sha(prior_path),core_modules=373,
  command=cmd,returncode=proc.returncode,stdout=proc.stdout,stderr=proc.stderr,seconds=time.monotonic()-start,
  script_sha256=sha(R/'scripts/ieantn.py'),hash_source_sha256=sha(R/'Tools/Hash.lean'),
  fingerprints=[dict(file=str(q.relative_to(R)),sha256=sha(q)) for q in fpfiles],controller_sha256=sha(Path(__file__)),
  scope='Genuine current ordinary core/hash/fingerprint tooling, including permanent Challenge sorry templates. Not official Comparator approval, source audit, proof completion, or PV.')
 out.parent.mkdir(parents=True,exist_ok=True);temp=out.with_name(out.name+'.tmp')
 with temp.open('x') as stream:json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
 os.replace(temp,out);directory=os.open(out.parent,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(directory)
 finally:os.close(directory)
 print(json.dumps({k:value[k] for k in ('status','core_modules','seconds')}))
if __name__=='__main__':main()
