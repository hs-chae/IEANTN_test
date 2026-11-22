#!/usr/bin/env python3
"""Rebuild the selected existing source-first C log closure with generic caches only."""
from pathlib import Path
import json,hashlib,subprocess,os,resource,time,argparse
B=Path(__file__).resolve().parent
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();O=a.out.resolve()
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
need(not O.exists(),'fresh output');ctx=json.loads((B.parent/'scripts/GENERIC_CONTEXT.json').read_text());need(sha(ctx['compiler'])==ctx['compiler_sha256'],'compilerpin');N=B.parents[2];PV=N/'Solutions/RamanujanSourcePV.v1';seen={};order=[]
def walk(mod):
 if mod.startswith(('Mathlib','Init','Lean','Std')):return
 if mod in seen:return
 ps=[r/(mod.replace('.','/')+'.lean')for r in[PV,N]];found=[p for p in ps if p.is_file()];need(bool(found),'missing source:'+mod);f=found[0];root=PV if f.is_relative_to(PV)else N;seen[mod]=(f,root)
 for line in f.read_text().splitlines():
  if line.startswith('import '):
   for imp in line[7:].split():
    if imp.startswith('--'):break
    walk(imp)
 order.append(mod)
walk('RamanujanPV.FiniteLogUpperExecute');O.mkdir(parents=True);(O/'objects').mkdir();(O/'logs').mkdir();env=os.environ.copy();env['LEAN_PATH']=':'.join([str(O/'objects'),*ctx['generic_libraries']]);records=[]
for mod in order:
 f,root=seen[mod];before=sha(f);out=O/'objects'/(mod.replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True);available=int(next(x.split()[1]for x in Path('/proc/meminfo').read_text().splitlines()if x.startswith('MemAvailable:')))*1024;need(available>=560*1024**3,'host512GiBreserve+48GiBproofadmission');cmd=['/usr/bin/time','-v','-o',str(O/'logs'/(mod+'.resources')),ctx['compiler'],'-j1','-R',str(root),str(f),'-o',str(out)];start=time.monotonic()
 def limits():resource.setrlimit(resource.RLIMIT_AS,(48*1024**3,48*1024**3))
 r=subprocess.run(cmd,cwd=root,env=env,text=True,capture_output=True,preexec_fn=limits);(O/'logs'/(mod+'.stdout')).write_text(r.stdout);(O/'logs'/(mod+'.stderr')).write_text(r.stderr);need(sha(f)==before,'sourcechanged');records.append({'module':mod,'source':str(f),'source_sha256':before,'returncode':r.returncode,'seconds':time.monotonic()-start,'command':cmd,'host_memavailable_before':available,'memory_limit':48*1024**3,'generic_cache_only':True});(O/'RESULT.json').write_text(json.dumps({'status':'RUNNING'if r.returncode==0 else'FAILED','modules':records},indent=2)+'\n');print(mod,r.returncode,round(records[-1]['seconds'],2),flush=True)
 if r.returncode:raise SystemExit(r.returncode)
(O/'RESULT.json').write_text(json.dumps({'status':'PASS_SOURCE_ONLY_ACTUAL_C_LOG_EXECUTION_CLOSURE','compiler_sha256':ctx['compiler_sha256'],'C_source_sha256':sha(PV/'c/verified_finite_log.c'),'historical_application_objects_used':False,'modules':records},indent=2)+'\n')
