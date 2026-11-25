#!/usr/bin/env python3
"""Fresh source-only full cube-consumer closure; explicit pinned generic library boundary."""
import argparse,hashlib,json,os,re,resource,subprocess,time,tempfile
from pathlib import Path

def need(c,m):
 if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def publish(path,data):
 need(not os.path.lexists(path),'Fresh acceptance path required')
 fd,name=tempfile.mkstemp(prefix='.acceptance-',dir=path.parent);q=Path(name)
 try:
  with os.fdopen(fd,'w') as f:f.write(json.dumps(data,indent=2,allow_nan=False)+'\n');f.flush();os.fsync(f.fileno())
  os.link(q,path)
 finally:q.unlink()
def read_json(path):
 def unique(pairs):
  out={}
  for k,v in pairs:need(k not in out,'Duplicate JSON key');out[k]=v
  return out
 return json.loads(path.read_bytes(),object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in ()).throw(ValueError('Nonfinite JSON '+x)))
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[4]);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--lane',choices=['early369'],default='early369');a=ap.parse_args();R=a.repository.resolve(strict=True);S=R/'Solutions/RH080Study.v1/estimates/early369';C=read_json(a.context);O=a.run.resolve();need(not O.exists(),'Fresh run required');pins=read_json(Path(__file__).with_name('DEPENDENCY_PINS.json'));need(C.get('generic_dependencies')==pins['generic_dependencies'],'Generic source pins differ');need(sha(Path(C['compiler']))==pins['compiler_sha256']==C.get('compiler_sha256'),'Pinned compiler bytes differ');version=subprocess.check_output([C['compiler'],'--version'],text=True).strip();need(version==pins['compiler_version']==C.get('compiler_version'),'Pinned compiler version differs');paths=C['generic_lean_path'].split(':');need(len(paths)==len(pins['generic_dependencies']),'Generic path population differs')
 for pp,dep in zip(paths,pins['generic_dependencies']):
  lib=Path(pp);need('/.lake/packages/' in pp and lib.is_dir(),'Generic library path outside pinned package layout');pkg=lib.parents[3];need(pkg.name==dep['name'],'Generic package order/name differs');rev=subprocess.check_output(['git','rev-parse','HEAD'],cwd=pkg,text=True).strip();dirty=subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=pkg,text=True);need(rev==dep['revision'] and not dirty,'Generic source revision or cleanliness differs')
 mi=Path('/proc/meminfo').read_text();available=int(next(l.split()[1] for l in mi.splitlines() if l.startswith('MemAvailable:')))*1024;need(available>=256*2**30,'Host256GiB reserve unavailable');O.mkdir(parents=True);src=O/'source';obj=O/'objects';logs=O/'logs';src.mkdir();obj.mkdir();logs.mkdir();manifest_path=S/'INPUT_MANIFEST.json';manifest_hash=sha(manifest_path);manifest=read_json(manifest_path);rows=[];seen=set()
 for row in manifest['modules']:
  m=row['module'];need(m not in seen,'Duplicate module identity');rel=Path(row['path']);need(not rel.is_absolute() and '..' not in rel.parts,'Unsafe provider path');p=R/rel;need(p.is_file() and not p.is_symlink(),'Missing regular source provider');need(p.resolve().is_relative_to(R),'Provider outside checkout');need(sha(p)==row['sha256'],'Source provider hash changed');ls=[]
  for line in p.read_text().splitlines():
   if line.startswith('import '):ls+=line.split('--')[0][7:].split()
  need(ls==row['imports'],'Actual imports changed')
  for x in ls:
   generic=x.startswith(('Mathlib.','Lean.','Std.','Init.','Batteries.','Aesop.','Qq.')) or x in ['Mathlib','Lean','Std','Init','Batteries','Aesop','Qq'];need(generic or x in seen,'Non-generic dependency absent or not topological: '+x)
  q=src/(m.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());seen.add(m);rows.append(dict(module=m,original=str(p),source_sha256=sha(q),imports=ls))
 need(manifest['root']=='EarlyAudit' and rows[-1]['module']=='EarlyAudit','Unexpected final consumer root')
 audit_module='EarlyAudit';audit_marker='EARLY369_AUDIT_PASS_6'
 plan=dict(status='FROZEN_SOURCE_ONLY_CLOSURE',modules=rows,compiler=C['compiler'],compiler_sha256=sha(Path(C['compiler'])),generic_lean_path=C['generic_lean_path'],predecessor_application_objects_used=False,host_meminfo=mi,per_process_AS_bytes=32*2**30,host_available_RAM_reserve_bytes=256*2**30,controller_sha256=sha(Path(__file__)));(O/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n');env=os.environ.copy();env['LEAN_PATH']=str(obj)+':'+C['generic_lean_path'];start=time.monotonic();results=[]
 for row in rows:
  m=row['module'];p=src/(m.replace('.','/')+'.lean');target=obj/(m.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True);stem=m.replace('.','_');out=logs/(stem+'.stdout');err=logs/(stem+'.stderr');cmd=['/usr/bin/prlimit','--as='+str(32*2**30),'--','/usr/bin/time','-v',C['compiler'],'-j2','--root='+str(src),'-o',str(target),str(p)];t=time.monotonic()
  with out.open('wb') as f,err.open('wb') as e:run=subprocess.run(cmd,env=env,stdout=f,stderr=e)
  item=dict(module=m,returncode=run.returncode,seconds=time.monotonic()-t,command=cmd,stdout_sha256=sha(out),stderr_sha256=sha(err),source_sha256=sha(p),object_sha256=sha(target) if target.exists() else None);results.append(item);(O/'PROGRESS.json').write_text(json.dumps(dict(compiled=len(results),required=len(rows),last=item['module'],returncode=run.returncode))+'\n')
  if run.returncode:
   (O/'FAILED.json').write_text(json.dumps(item,indent=2)+'\n');print(out.read_text()[-5000:]);raise SystemExit(run.returncode)
  need(sha(Path(row['original']))==row['source_sha256'],'Original source changed during replay')
 audit=(logs/(audit_module+'.stdout')).read_text();need(audit_marker in audit,'Missing final value/type/axiom audit');need('sorryAx' not in audit and 'Lean.ofReduceBool' not in audit,'Unaccepted axioms');rss=[];cpu=[];kills=[]
 for f in logs.glob('*.stderr'):
  t=f.read_text();rss += [int(x) for x in re.findall(r'Maximum resident set size \(kbytes\): (\d+)',t)];cpu += [dict(log=f.name,user=float(u),system=float(v)) for u,v in re.findall(r'User time \(seconds\): ([0-9.]+)\s+System time \(seconds\): ([0-9.]+)',t)];kills += [f.name for x in re.findall('terminated by signal 9',t)]
 for row in rows:need(sha(Path(row['original']))==row['source_sha256'],'Source changed after compilation')
 need(sha(Path(__file__))==plan['controller_sha256'],'Controller changed during replay');need(sha(manifest_path)==manifest_hash,'Input manifest changed during replay')
 receipt=dict(status='PASS_FRESH_COMPLETE_SOURCE_CLOSURE_AND_EXACT_VALUE_INPUT_AXIOM_AUDITS',lane=a.lane,modules=len(rows),seconds=time.monotonic()-start,maximum_recorded_per_process_GNU_RSS_kib=max(rss),CPU_seconds_sum=sum(x['user']+x['system'] for x in cpu),sampled_aggregate_RSS_not_measured=True,final_directory_bytes=sum(p.stat().st_size for p in O.rglob('*') if p.is_file()),peak_disk_not_measured=True,observed_sigkill_logs=kills,axioms=['propext','Classical.choice','Quot.sound'],source_first_PV=False,source_assumptions='EXACT ordinary RH + SchoenfeldRHTheta.v1.refined_theta + Buthe.v1.theorem_2_theta + Buthe.v1.theorem_2_theta_lower. New exact timely .96699/n>=369. Hybrid conclusion composes explicit v3 early and prior v2 .9669924/e8 conclusion predicates. No added source premise; old results and outcomes unchanged.',input_manifest_sha256=manifest_hash,plan_sha256=sha(O/'PLAN.json'),commands=results,controller_sha256=sha(Path(__file__)));need(not kills,'ObservedSIGKILL');publish(O/'RESULT.json',receipt);print(json.dumps({k:receipt[k] for k in ['status','modules','seconds','maximum_recorded_per_process_GNU_RSS_kib','CPU_seconds_sum','final_directory_bytes']}))
if __name__=='__main__':main()
