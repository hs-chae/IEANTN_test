#!/usr/bin/env python3
"""Compile new track modules against explicitly named fresh source replays."""
from pathlib import Path
import argparse,hashlib,json,os,resource,subprocess,time
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--source',type=Path,default=B);p.add_argument('--lib',type=Path,action='append',default=[]);p.add_argument('modules',nargs='+');a=p.parse_args()
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
O=a.out.resolve();need(not O.exists(),'fresh output required');ctx=json.loads((B.parent/'scripts/GENERIC_CONTEXT.json').read_text());need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compiler identity');O.mkdir(parents=True);(O/'objects').mkdir();(O/'logs').mkdir();merged=[]
for lib in a.lib:
 need(lib.is_dir(),'missing explicit source replay library')
 for source_object in lib.rglob('*.olean'):
  target=O/'objects'/source_object.relative_to(lib)
  if target.exists():need(sha(target)==sha(source_object),'conflicting fresh source objects')
  else:target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(source_object.resolve())
  merged.append({'object':str(source_object),'sha256':sha(source_object)})
(O/'MERGED_OBJECTS.json').write_text(json.dumps(merged,indent=2)+'\n')
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[O/'objects',*a.lib,*ctx['generic_libraries']]));records=[]
for module in a.modules:
 need('/'not in module and '..'not in module,'module identity');src=a.source/(module.replace('.','/')+'.lean');before=sha(src);own_output=O/'objects'/(module.replace('.','/')+'.olean');own_output.parent.mkdir(parents=True,exist_ok=True)
 if own_output.is_symlink():own_output.unlink()
 available=int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))*1024;need(available>=528*1024**3,'16GiB process+512GiB host reserve');cmd=['/usr/bin/time','-v','-o',str(O/'logs'/(module+'.resources')),ctx['compiler'],'-j1','-R',str(a.source),' -o'.strip(),str(own_output),str(src)];start=time.monotonic()
 def limits():resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,16*1024**3))
 r=subprocess.run(cmd,cwd=a.source,env=env,capture_output=True,text=True,preexec_fn=limits);(O/'logs'/(module+'.stdout')).write_text(r.stdout);(O/'logs'/(module+'.stderr')).write_text(r.stderr);need(sha(src)==before,'source mutation during compile');records.append({'module':module,'source':str(src),'source_sha256':before,'returncode':r.returncode,'seconds':time.monotonic()-start,'command':cmd,'host_memavailable_before':available,'memory_limit':16*1024**3});(O/'RESULT.json').write_text(json.dumps({'status':'RUNNING'if r.returncode==0 else'FAILED','libraries':list(map(str,a.lib)),'modules':records},indent=2)+'\n');print(module,r.returncode,round(records[-1]['seconds'],2),flush=True)
 if r.returncode:print(r.stdout);print(r.stderr);raise SystemExit(r.returncode)
(O/'RESULT.json').write_text(json.dumps({'status':'PASS','compiler_sha256':ctx['compiler_sha256'],'libraries':list(map(str,a.lib)),'modules':records},indent=2)+'\n')
