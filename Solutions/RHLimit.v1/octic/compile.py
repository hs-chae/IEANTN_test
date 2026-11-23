#!/usr/bin/env python3
"""Incremental source build with recorded, source/object-checked shared bank."""
from pathlib import Path
import argparse,hashlib,json,os,resource,subprocess,time
B=Path(__file__).resolve().parent;N=B.parents[2]
BASE=Path('/data/ivy-rh-continuation-20261122/integration/public-final-v2/base')
CONTEXT=N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  out={}
  for k,v in rows:need(k not in out,'duplicate JSON key');out[k]=v
  return out
 def number(raw):
  v=float(raw);need(abs(v)!=float('inf'),'overflowing JSON float');return v
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_float=number,parse_constant=lambda x:(_ for _ in()).throw(ValueError('nonfinite JSON')))
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--module',action='append',required=True);p.add_argument('--support-run',type=Path,action='append',default=[]);a=p.parse_args();need(not a.out.exists(),'fresh output');c=read(CONTEXT);need(sha(c['compiler'])==c['compiler_sha256'],'compiler identity');need(sha(BASE/'BUILD.json')=='6f72bc4d2ba7dd34a8410ec53c0f0072a8c6d4d47f0bebb2613d7a7cc0c518cf','immutable baseline receipt');j=read(BASE/'BUILD.json');need(j['status']=='PASS'and len(j['modules'])==111,'base status/count');objects=[]
for x in j['modules']:
 src=Path(x['command'][-1]);obj=BASE/'objects'/(x['module'].replace('.','/')+'.olean');need(sha(src)==x['source_sha256']and sha(obj)==x['object_sha256']and x['returncode']==0,'base source/object identity');objects.append(str(obj.relative_to(BASE/'objects')))
need({str(p.relative_to(BASE/'objects'))for p in(BASE/'objects').rglob('*')if p.is_file()}==set(objects),'base membership')
support=[]
for root in a.support_run:
 q=read(root/'RESULT.json');need(q['status']=='PASS'and q['compiler_sha256']==c['compiler_sha256'],'supportstatus')
 for x in q['modules']:
  need(type(x['returncode'])is int and x['returncode']==0 and sha(B/(x['module'].replace('.','/')+'.lean'))==x['source_sha256']and sha(root/'objects'/(x['module'].replace('.','/')+'.olean'))==x['object_sha256'],'supportsource/objectidentity')
 support.append(str(root/'objects'))
a.out.mkdir();(a.out/'objects').mkdir();(a.out/'logs').mkdir();(a.out/'source').mkdir();env=os.environ.copy();env['LEAN_PATH']=':'.join([str(a.out/'objects'),*support,str(BASE/'objects'),*c['generic_libraries']]);rows=[]
for mod in a.module:
 src=B/(mod.replace('.','/')+'.lean');cp=a.out/'source'/src.name;cp.write_bytes(src.read_bytes());obj=a.out/'objects'/src.with_suffix('.olean').name;cmd=[c['compiler'],'--root='+str(a.out/'source'),'-j8','-o',str(obj),str(cp)];st=time.monotonic()
 def limit():resource.setrlimit(resource.RLIMIT_AS,(80*1024**3,80*1024**3))
 run=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=a.out/'source',env=env,text=True,capture_output=True,preexec_fn=limit);(a.out/'logs'/(mod+'.stdout')).write_text(run.stdout);(a.out/'logs'/(mod+'.stderr')).write_text(run.stderr);rows.append({'module':mod,'source_sha256':sha(src),'command':cmd,'returncode':run.returncode,'seconds':time.monotonic()-st,'object_sha256':sha(obj)if obj.exists()and run.returncode==0 else None});(a.out/'RESULT.json').write_text(json.dumps({'status':'RUNNING'if run.returncode==0 else'FAIL','modules':rows,'base_receipt_sha256':sha(BASE/'BUILD.json'),'compiler_sha256':c['compiler_sha256'],'controller_sha256':sha(__file__),'scope':'Incremental compile; recorded source/object-checked existing111modulebank, not a fresh complete closure replay.'},indent=2)+'\n');print(mod,run.returncode,round(rows[-1]['seconds'],2),flush=True)
 if run.returncode:print(run.stdout[-5000:]);raise SystemExit(run.returncode)
(a.out/'RESULT.json').write_text(json.dumps({'status':'PASS','modules':rows,'base_receipt_sha256':sha(BASE/'BUILD.json'),'compiler_sha256':c['compiler_sha256'],'controller_sha256':sha(__file__),'scope':'Incremental compile; recorded source/object-checked existing111modulebank, not a fresh complete closure replay.'},indent=2)+'\n')
