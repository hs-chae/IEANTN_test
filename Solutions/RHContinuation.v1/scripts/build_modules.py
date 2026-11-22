#!/usr/bin/env python3
"""Compile explicit source modules using pinned generic libraries and declared objects."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,time

def need(ok,message):
 if not ok:raise ValueError(message)
def read(path):
 def pairs(rows):
  result={}
  for key,value in rows:
   need(key not in result,'duplicate JSON key');result[key]=value
  return result
 return json.loads(Path(path).read_bytes(),object_pairs_hook=pairs,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def publish(path,value):
 temp=path.with_name('.'+path.name+'.pending');temp.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n');os.replace(temp,path)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--source',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--module',action='append',default=[]);p.add_argument('--extra-library',action='append',default=[]);a=p.parse_args();reference=Path(__file__).parent/'GENERIC_CONTEXT.json';pinned=read(reference);ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',reference)));src=a.source.resolve();out=a.out.resolve();own_hash=sha(__file__)
 need(a.module and len(set(a.module))==len(a.module),'nonempty distinct application module list required')
 for mod in a.module:need(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',mod)is not None,'invalid module name')
 need(ctx['compiler_sha256']==pinned['compiler_sha256']and[(d['name'],d['revision'])for d in ctx['generic_dependencies']]==[(d['name'],d['revision'])for d in pinned['generic_dependencies']],'relocation changes pinned identities')
 need(sha(ctx['compiler'])==ctx['compiler_sha256'],'pinned compiler differs')
 for dep in ctx['generic_dependencies']:
  actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep['path'],text=True).strip();need(actual==dep['revision'],'generic revision differs:'+dep['name'])
 need(src.is_dir(),'source directory missing')
 for mod in a.module:need((src/(mod.replace('.','/')+'.lean')).is_file(),'source module missing:'+mod)
 need(not out.exists(),'fresh output required');out.mkdir(parents=True);(out/'objects').mkdir();(out/'logs').mkdir();extras=[]
 for entry in a.extra_library:
  lib=Path(entry).resolve();need(lib.is_dir(),'declared shared library missing');files=[]
  for original in sorted(lib.rglob('*')):
   if not original.is_file():continue
   relative=original.relative_to(lib);target=out/'objects'/relative;raw=original.read_bytes();need(not target.exists()or target.read_bytes()==raw,'shared object collision:'+str(relative));target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw);files.append({'path':str(relative),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()})
  extras.append({'library':str(lib),'files':files})
 publish(out/'EXTRA_LIBRARIES.json',extras);env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'objects'),*ctx['generic_libraries']]);rows=[]
 for mod in a.module:
  source=src/(mod.replace('.','/')+'.lean');obj=out/'objects'/(mod.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);before=sha(source);start=time.monotonic();command=[ctx['compiler'],'-o',str(obj),str(source)];r=subprocess.run(['/usr/bin/time','-v',*command],cwd=src,env=env,text=True,capture_output=True);(out/'logs'/(mod+'.stdout')).write_text(r.stdout);(out/'logs'/(mod+'.stderr')).write_text(r.stderr);need(sha(source)==before,'source changed during compilation');row={'module':mod,'source_sha256':before,'command':command,'returncode':r.returncode,'seconds':time.monotonic()-start,'object_sha256':sha(obj)if r.returncode==0 and obj.is_file()else None};rows.append(row);publish(out/'BUILD.json',{'status':'RUNNING'if r.returncode==0 else'FAIL','compiler_sha256':ctx['compiler_sha256'],'validator_sha256':own_hash,'extra_libraries':a.extra_library,'modules':rows});print(mod,r.returncode,round(row['seconds'],2),flush=True)
  if r.returncode:raise SystemExit(r.returncode)
 need(sha(__file__)==own_hash,'build helper changed while running');publish(out/'BUILD.json',{'status':'PASS','compiler_sha256':ctx['compiler_sha256'],'validator_sha256':own_hash,'extra_libraries':a.extra_library,'modules':rows})
if __name__=='__main__':main()
