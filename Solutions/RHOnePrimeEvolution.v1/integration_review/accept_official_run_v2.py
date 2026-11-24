#!/usr/bin/env python3
"""Check the current genuine core/hash/fingerprint evidence, then publish atomically.
Bookkeeping only: no Comparator approval, mathematical source audit or PV.
"""
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
 def pairs(items):
  out={}
  for k,v in items:
   if k in out:raise ValueError('Duplicate JSON key '+k)
   out[k]=v
  return out
 return json.loads(p.read_text(),object_pairs_hook=pairs)
def core_universe(R):
 seen={};visiting=set()
 def visit(module):
  if not(module=='IEANTN' or module.startswith('IEANTN.')):return
  if module in visiting:raise ValueError('Core import cycle')
  if module in seen:return
  file=R/(module.replace('.','/')+'.lean')
  if not file.is_file():raise ValueError('Missing genuine core module '+module)
  visiting.add(module)
  for line in file.read_text().split('\n'):
   match=re.match(r'^(?:public\s+)?import\s+(.+)',line)
   if match:
    for dep in match[1].split('--',1)[0].split():visit(dep)
  visiting.remove(module);seen[module]=file
 visit('IEANTN');return seen

def main():
 p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
 p.add_argument('--repository',type=Path,required=True);p.add_argument('--execution',type=Path,required=True);p.add_argument('--output',type=Path,required=True)
 a=p.parse_args();R=a.repository.resolve(strict=True);E=a.execution.resolve(strict=True);out=a.output.resolve()
 if out.exists():raise ValueError('Fresh acceptance destination required')
 r=load(E);plan=load(E.parent/'PLAN.json');universe=core_universe(R)
 if r['status']!='PASS_GENUINE_LAKE_CORE_HASH_FINGERPRINT' or r['failure'] is not None:raise ValueError('Official execution did not pass')
 selected={q['module']:q for q in plan['modules']}
 if len(selected)!=len(plan['modules']) or set(selected)!=set(universe):raise ValueError('Current complete core module universe differs')
 if r['completed']!=len(universe) or r['core_modules']!=len(universe):raise ValueError('Incomplete current core execution')
 for name,file in universe.items():
  q=selected[name]
  if Path(q['file']).resolve()!=file.resolve() or sha(file)!=q['source_sha256']:raise ValueError('Core source mismatch '+name)
 lake=Path(plan['lake'])
 if sha(lake)!=plan['lake_sha256']:raise ValueError('Recorded Lake binary changed')
 prior=r['reused_core'];core_receipt=E;builds=r['builds']
 if prior is not None:
  core_receipt=Path(prior['receipt']).resolve(strict=True)
  if sha(core_receipt)!=prior['sha256']:raise ValueError('Prior execution hash mismatch')
  old=load(core_receipt);oldplan=load(core_receipt.parent/'PLAN.json');oldtable={q['module']:q for q in oldplan['modules']}
  if old['completed']!=len(universe) or old['core_modules']!=len(universe) or set(oldtable)!=set(selected):raise ValueError('Prior core coverage differs')
  if any(oldtable[k]['source_sha256']!=selected[k]['source_sha256'] for k in selected):raise ValueError('Prior core source identities differ')
  builds=old['builds']
 table={q['module']:q for q in builds}
 if len(table)!=len(builds) or set(table)!=set(universe):raise ValueError('Missing or duplicate actual core invocation')
 for name,q in table.items():
  if q['returncode']!=0 or q['command'][-3:]!=[str(lake),'build','+'+name+':olean']:raise ValueError('Invalid genuine core command '+name)
  for stream in ['stdout','stderr']:
   if sha(core_receipt.parent/'logs'/(name+'.'+stream))!=q[stream+'_sha256']:raise ValueError('Core execution log changed '+name)
 steps=r['subsequent']
 if [q['name'] for q in steps]!=['hash-executable','fingerprint','fingerprint-check']:raise ValueError('Missing genuine subsequent commands')
 for q in steps:
  if q['returncode']!=0:raise ValueError('Official command failed')
  for stream in ['stdout','stderr']:
   if sha(E.parent/'logs'/(q['name']+'.'+stream))!=q[stream+'_sha256']:raise ValueError('Official command log changed')
 env=os.environ.copy();env['PATH']=str(lake.parent)+':'+env['PATH'];env['LEAN_NUM_THREADS']='4'
 cmd=['python3','scripts/ieantn.py','fingerprint','--check'];start=time.monotonic();proc=subprocess.run(cmd,cwd=R,env=env,text=True,capture_output=True)
 if proc.returncode or proc.stdout.strip()!='ok  statement fingerprints':raise ValueError('Fresh genuine fingerprint readback failed')
 value={'status':'PASS_ATOMICALLY_CHECKED_CURRENT_GENUINE_BOOKKEEPING','execution_sha256':sha(E),'core_plan_sha256':sha(E.parent/'PLAN.json'),'core_modules':len(universe),'actual_core_invocations':len(builds),'reused_core_sha256':sha(core_receipt) if prior else None,'fresh_readback_command':cmd,'readback_returncode':proc.returncode,'readback_stdout':proc.stdout,'seconds':time.monotonic()-start,'script_sha256':sha(R/'scripts/ieantn.py'),'hash_source_sha256':sha(R/'Tools/Hash.lean'),'controller_sha256':sha(Path(__file__)),'fingerprints':[{'path':str(q.relative_to(R)),'sha256':sha(q)} for q in sorted((R/'IEANTN/Nodes').glob('*/*/fingerprints.json'))],'scope':'Genuine ordinary core/hash/fingerprints, including permanent Challenge placeholders. Not Comparator approval, solution proof completion, source audit, or source-first PV.'}
 out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_name(out.name+'.new')
 with tmp.open('x') as f:json.dump(value,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 os.replace(tmp,out);fd=os.open(out.parent,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(fd)
 finally:os.close(fd)
 print(json.dumps({k:value[k] for k in ['status','core_modules','seconds']}))
if __name__=='__main__':
 try:main()
 except (ValueError,KeyError,OSError,subprocess.CalledProcessError) as e:raise SystemExit(str(e))
