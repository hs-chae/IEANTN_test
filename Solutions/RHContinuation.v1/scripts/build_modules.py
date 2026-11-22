#!/usr/bin/env python3
from pathlib import Path
import argparse,json,os,subprocess,hashlib,time
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--source',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--module',action='append',default=[]);p.add_argument('--extra-library',action='append',default=[]);a=p.parse_args();ctx=json.loads((Path(__file__).parent/'GENERIC_CONTEXT.json').read_text());src=a.source.resolve();out=a.out.resolve()
if not a.module:raise ValueError('at least one application module required')
if hashlib.sha256(Path(ctx['compiler']).read_bytes()).hexdigest()!=ctx['compiler_sha256']:
 raise ValueError('pinned compiler identity differs')
for dep in ctx['generic_dependencies']:
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=dep['path'],text=True).strip()
 if actual!=dep['revision']:raise ValueError('generic dependency revision differs:'+dep['name'])
if out.exists():raise ValueError('fresh output required')
out.mkdir(parents=True);(out/'objects').mkdir();(out/'logs').mkdir();env=os.environ.copy();env['LEAN_PATH']=':'.join([str(out/'objects'),*a.extra_library,*ctx['generic_libraries']]);rows=[]
for mod in a.module:
 f=src/(mod.replace('.','/')+'.lean');obj=out/'objects'/(mod.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True);start=time.monotonic();cmd=[ctx['compiler'],'-o',str(obj),str(f)];r=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=src,env=env,text=True,capture_output=True);(out/'logs'/(mod+'.stdout')).write_text(r.stdout);(out/'logs'/(mod+'.stderr')).write_text(r.stderr);row={'module':mod,'source_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'command':cmd,'returncode':r.returncode,'seconds':time.monotonic()-start};rows.append(row);(out/'BUILD.json').write_text(json.dumps({'status':'RUNNING'if not r.returncode else'FAIL','compiler_sha256':ctx['compiler_sha256'],'extra_libraries':a.extra_library,'modules':rows},indent=2)+'\n');print(mod,r.returncode,round(row['seconds'],2),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
(out/'BUILD.json').write_text(json.dumps({'status':'PASS','compiler_sha256':ctx['compiler_sha256'],'extra_libraries':a.extra_library,'modules':rows},indent=2)+'\n')
