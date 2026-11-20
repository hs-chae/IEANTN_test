#!/usr/bin/env python3
"""Fresh application build with pinned generic dependencies; no old app .oleans.
Either supply the original context or a context with clean-machine paths to
exactly the SAME dependency commits. All context and source hashes are retained.
"""
import argparse, hashlib, json, os, pathlib, re, resource, subprocess, time
ROOTS=['RamanujanPV']
def main():
 p=argparse.ArgumentParser();p.add_argument('--context',type=pathlib.Path,required=True);p.add_argument('--out',type=pathlib.Path,required=True);p.add_argument('--root',action='append');p.add_argument('--cpus',default='0,1,2,3');a=p.parse_args();s=pathlib.Path(__file__).resolve().parents[1];network=s.parents[1];c=json.loads(a.context.read_text());out=a.out.resolve()
 if out.exists():raise ValueError('fresh output directory')
 lean=pathlib.Path(c['compiler'])
 if hashlib.sha256(lean.read_bytes()).hexdigest()!=c['compiler_sha256']:raise ValueError('pinned compiler')
 libs=[]
 for dep in c['generic_dependencies']:
  if not dep['library_present']:continue
  d=pathlib.Path(dep['path']);actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=d,text=True).strip()
  if actual!=dep['revision'] or subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=d,text=True):raise ValueError('generic dependency identity '+dep['name'])
  lib=d/'.lake/build/lib/lean'
  if not lib.is_dir():raise ValueError('generic library missing')
  libs.append(str(lib))
 roots=a.root or ROOTS;order=[];seen=set();visiting=set()
 def resolve(m):
  base=network if m.startswith('IEANTN.') else s;p=base/pathlib.Path(*m.split('.')).with_suffix('.lean');return base,p
 def visit(m):
  if m in seen:return
  base,source=resolve(m)
  if not source.is_file():
   if any((pathlib.Path(l)/pathlib.Path(*m.split('.')).with_suffix('.olean')).is_file() for l in libs):return
   raise ValueError('unresolved import '+m)
  if m in visiting:raise ValueError('import cycle')
  visiting.add(m);txt=source.read_text()
  for line in txt.splitlines():
   if line.startswith('import '):
    for dep in line[7:].split():visit(dep)
  visiting.remove(m);seen.add(m);order.append((m,base,source))
 for m in roots:visit(m)
 out.mkdir(parents=True);payloads={}
 for _,_,src in order:
  for rel in re.findall(r'include_str\s+"([^"]+)"',src.read_text()):
   f=(src.parent/rel).resolve();payloads[str(f)]=hashlib.sha256(f.read_bytes()).hexdigest()
 (out/'PAYLOADS.json').write_text(json.dumps(payloads,indent=2)+'\n')
 objects=out/'lean';objects.mkdir();audit=out/'audit';audit.mkdir();env=dict(os.environ,LEAN_PATH=os.pathsep.join([str(objects),*libs]));records=[];cpus={int(x) for x in a.cpus.split(',')}
 if not cpus or not cpus<=os.sched_getaffinity(0):raise ValueError('cpu availability')
 def limits():resource.setrlimit(resource.RLIMIT_AS,(48<<30,48<<30));os.sched_setaffinity(0,cpus)
 for m,base,source in order:
  d=audit/m;d.mkdir();obj=objects/pathlib.Path(*m.split('.')).with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);cmd=[str(lean),'-j1','-R',str(base),str(source),'-o',str(obj)];t=time.monotonic();before=source.read_bytes();before_sha=hashlib.sha256(before).hexdigest();(d/'source.lean').write_bytes(before)
  with(d/'stdout').open('wb')as so,(d/'stderr').open('wb')as se:x=subprocess.run(['/usr/bin/time','-v','-o',str(d/'rusage'),*cmd],cwd=base,env=env,preexec_fn=limits,stdout=so,stderr=se)
  rec={'module':m,'source_sha256':before_sha,'source_unchanged_during_compile':before_sha==hashlib.sha256(source.read_bytes()).hexdigest(),'command':cmd,'exit_code':x.returncode,'seconds':time.monotonic()-t};(d/'RUN.json').write_text(json.dumps(rec,indent=2)+'\n');records.append(rec);print(json.dumps(rec),flush=True)
  if x.returncode or not rec['source_unchanged_during_compile']:raise RuntimeError('Lean build/source-drift failure '+m)
 for path,h in payloads.items():
  if hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()!=h:raise ValueError('selected source payload changed during proof build')
 (out/'RESULT.json').write_text(json.dumps({'status':'FRESH_SELECTED_APPLICATION_BUILD_PASS','roots':roots,'compiler_sha256':c['compiler_sha256'],'context_sha256':hashlib.sha256(a.context.read_bytes()).hexdigest(),'records':records,'old_application_objects_used':False},indent=2)+'\n')
if __name__=='__main__':main()
