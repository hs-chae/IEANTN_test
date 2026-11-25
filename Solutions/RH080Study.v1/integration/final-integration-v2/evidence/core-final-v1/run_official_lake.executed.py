#!/usr/bin/env python3
"""Run genuine Lake on topologically admitted core modules, then official fingerprints.
Uses at most four Lake invocations, with application dependencies completed first.
The ordinary IEANTN umbrella deliberately includes Challenge declarations with
permanent sorry templates. This run is not a proof audit of those challenges.
"""
import argparse, hashlib, json, os, re, subprocess, time
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic_json(path,value):
 temporary=path.with_name(path.name+'.tmp')
 with temporary.open('x') as stream:json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
 os.replace(temporary,path);directory=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(directory)
 finally:os.close(directory)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--repository',type=Path,required=True);p.add_argument('--run',type=Path,required=True);p.add_argument('--reuse-core-receipt',type=Path);a=p.parse_args()
 R=a.repository.resolve(strict=True);D=a.run.resolve();D.mkdir(exist_ok=True);S=R/'Solutions/RHOnePrimeEvolution.v1'
 C=json.loads((S/'scripts/LOCAL_CONTEXT.json').read_text());lake=str(Path(C['compiler']).parent/'lake')
 for dep in C['generic_dependency_versions']:
  pkg=(R/'.lake/packages'/dep['name']).resolve(strict=True)
  if pkg==Path(dep['path']).resolve() or not (pkg.parent/'COPY_RECEIPT.json').is_file():
   raise SystemExit('Private generic package copies required before writable hash/native-link builds; run isolate_lake_packages.py')
  rev=subprocess.check_output(['git','-C',str(pkg),'rev-parse','HEAD'],text=True).strip()
  clean=subprocess.check_output(['git','-C',str(pkg),'status','--porcelain','--untracked-files=no'],text=True)
  if rev!=dep['revision'] or clean:raise SystemExit('Private generic source pin mismatch '+dep['name'])
 files={'.'.join(f.relative_to(R).with_suffix('').parts):f for f in (R/'IEANTN').rglob('*.lean')};files['IEANTN']=R/'IEANTN.lean'
 order=[];deps={};seen=set();active_set=set()
 def visit(m):
  if m in seen:return
  if m in active_set:raise SystemExit('Cycle '+m)
  if m not in files:return
  active_set.add(m);ds=[]
  for line in files[m].read_text().split('\n'):
   q=re.match(r'^(?:public\s+)?import\s+(.+)',line)
   if q:ds.extend(q[1].split('--',1)[0].split())
  deps[m]=[d for d in ds if d in files]
  for d in deps[m]:visit(d)
  active_set.remove(m);seen.add(m);order.append(m)
 visit('IEANTN')
 plan=[dict(module=m,file=str(files[m]),source_sha256=sha(files[m]),deps=deps[m]) for m in order]
 (D/'PLAN.json').write_text(json.dumps(dict(modules=plan,lake=lake,lake_sha256=sha(Path(lake)),compiler=C['compiler'],mathlib_commit=C['mathlib_commit'],concurrency=4,scope='Genuine ordinary core build including intentional Challenge sorry templates. Separate from actual Solution theorem proof audits.'),indent=2)+'\n')
 (D/'run_official_lake.executed.py').write_bytes(Path(__file__).read_bytes())
 logs=D/'logs';logs.mkdir(exist_ok=True);env=os.environ.copy();env['LEAN_NUM_THREADS']='4';env['PATH']=str(Path(lake).parent)+':'+env['PATH']
 waiting=order.copy();active={};done=set();rows=[];failure=None;start=time.monotonic();reused_core=None
 if a.reuse_core_receipt:
  receipt=a.reuse_core_receipt.resolve(strict=True);prior=json.loads(receipt.read_text());priorplan=json.loads((receipt.parent/'PLAN.json').read_text())
  previous={r['module']:r for r in priorplan['modules']}
  if prior['completed']!=len(order) or prior['core_modules']!=len(order) or any(r['returncode'] for r in prior['builds']) or set(previous)!=set(order):
   raise SystemExit('Requested prior ordinary core receipt is incomplete')
  for row in plan:
   if previous[row['module']]['source_sha256']!=row['source_sha256']:raise SystemExit('Prior ordinary core source differs '+row['module'])
   if not (R/'.lake/build/lib/lean'/(row['module'].replace('.','/')+'.olean')).is_file():raise SystemExit('Prior core object missing '+row['module'])
  reused_core=dict(receipt=str(receipt),sha256=sha(receipt),completed_modules=len(order),scope='Earlier genuine sequential Lake core build, reused explicitly; new run executes native hash build and genuine fingerprints.')
  done=set(order);waiting=[]
 while waiting or active:
  for m in waiting.copy():
   if failure or len(active)>=4:break
   if not all(d in done for d in deps[m]):continue
   available=int(re.search(r'MemAvailable:\s+(\d+)',Path('/proc/meminfo').read_text())[1])*1024
   if available<256*1024**3:failure='Host RAM admission reserve';break
   out=(logs/(m+'.stdout')).open('wb');err=(logs/(m+'.stderr')).open('wb')
   cmd=['/usr/bin/prlimit','--as=68719476736','--','/usr/bin/time','-v',lake,'build','+'+m+':olean']
   proc=subprocess.Popen(cmd,cwd=R,env=env,stdout=out,stderr=err)
   active[m]=(proc,out,err,cmd,time.monotonic());waiting.remove(m)
  for m,item in list(active.items()):
   proc,out,err,cmd,began=item;rc=proc.poll()
   if rc is None:continue
   out.close();err.close();error=(logs/(m+'.stderr')).read_text();rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',error)
   rows.append(dict(module=m,returncode=rc,command=cmd,seconds=time.monotonic()-began,peak_child_RSS_KiB=int(rss[1]) if rss else None,stdout_sha256=sha(logs/(m+'.stdout')),stderr_sha256=sha(logs/(m+'.stderr'))))
   del active[m]
   if rc:failure='Lake failed '+m
   else:done.add(m)
   (D/'PROGRESS.json').write_text(json.dumps(dict(finished=len(done),total=len(order),active=list(active),failure=failure,builds=rows),indent=2)+'\n')
  if failure and not active:break
  time.sleep(.2)
 if not failure:
  for row in plan:
   if sha(Path(row['file']))!=row['source_sha256']:failure='Core source changed during official build: '+row['module'];break
 subsequent=[]
 if not failure:
  for name,cmd in [('hash-executable',[lake,'build','ieantn_hash']),('fingerprint',['python3','scripts/ieantn.py','fingerprint']),('fingerprint-check',['python3','scripts/ieantn.py','fingerprint','--check'])]:
   t=time.monotonic()
   command=['/usr/bin/prlimit','--as=68719476736','--','/usr/bin/time','-v']+cmd
   with (logs/(name+'.stdout')).open('wb') as out,(logs/(name+'.stderr')).open('wb') as err:proc=subprocess.run(command,cwd=R,env=env,stdout=out,stderr=err)
   subsequent.append(dict(name=name,command=command,returncode=proc.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(logs/(name+'.stdout')),stderr_sha256=sha(logs/(name+'.stderr'))))
   if proc.returncode:failure='Official step failed '+name;break
 result=dict(status='FAILED' if failure else 'PASS_GENUINE_LAKE_CORE_HASH_FINGERPRINT',failure=failure,core_modules=len(order),completed=len(done),seconds=time.monotonic()-start,builds=rows,reused_core=reused_core,subsequent=subsequent,scope='Official bookkeeping/core build includes permanent Challenge sorries. It is not proof completion, PV, or source audit.')
 atomic_json(D/'RESULT.json',result);print(json.dumps({k:result[k] for k in ('status','completed','core_modules','seconds','failure')}))
 if failure:raise SystemExit(1)
if __name__=='__main__':main()
