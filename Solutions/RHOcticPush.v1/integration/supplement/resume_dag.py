"""Strict same-campaign reuse of completed downward-closed DAG leaves.
An interrupted attempt remains interrupted; no receipt is backfilled into it.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess
HERE=Path(__file__).resolve().parent
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate key');d[k]=v
  return d
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def validate_reuse(old,m,ctx,primary):
 old=Path(old).resolve();need((old/'INTERRUPTION.json').is_file()and not(old/'RESULT.json').exists(),'only explicitly interrupted original source attempt')
 need(read(old/'INTERRUPTION.json')['status']=='INTERRUPTED_EXIT143_NO_ACCEPTANCE','interruption identity')
 need(sha(old/'reproduce.executed.py')==sha(HERE/'reproduce.py'),'original unmodified controller')
 need(sha(old/'SOURCE_CLOSURE.executed.json')==sha(HERE/'capture/SOURCE_CLOSURE.json'),'same exact165 mathematical source freeze')
 b=read(old/'BUILD.json');need(b['status']=='RUNNING','interrupted partial status');records={x['module']:x for x in b['modules']};need(len(records)==len(b['modules'])>0,'unique completed identities')
 need(set(records)<={x['module']for x in m['modules']},'foreign completed source');maps=dict(primary);done=set(primary);ordered=[];probes=[];ad=read(old/'RESOURCE_ADMISSION.json');memory=ad['per_job_address_space_cap_bytes'];threads=2
 need(memory==64<<30 and ad['max_parallel_jobs']==8,'original resource policy')
 for want in m['modules']:
  mod=want['module']
  if mod not in records:continue
  row=records[mod];need(set(want['application_imports'])<=done,'completed set is not downward closed');need(type(row['returncode'])is int and row['returncode']==0,'completed source failed')
  rel=mod.replace('.','/');src=old/'source'/(rel+'.lean');obj=old/'objects'/(rel+'.olean');need(src.is_file()and obj.is_file()and not src.is_symlink()and not obj.is_symlink(),'owned source/object')
  need(sha(src)==want['sha256']==row['source_sha256']and sha(obj)==row['object_sha256'],'exact same-source fresh leaf')
  cmd=['/usr/bin/prlimit','--as='+str(memory),'--','/usr/bin/time','-v',ctx['compiler'],'--root='+str(old/'source'),'-j'+str(threads),'-o',str(obj),str(src)];need(row['command']==cmd,'original actual compiler command')
  for suffix in ['stdout','stderr']:need(sha(old/'logs'/(mod+'.'+suffix))==row[suffix+'_sha256'],'original compiler log')
  dep=[ctx['compiler'],'--root='+str(old/'source'),'--deps',str(src)];env=os.environ.copy();env['LEAN_PATH']=':'.join([str(old/'union'),*ctx['generic_libraries']]);cp=subprocess.run(dep,cwd=old/'source',env=env,capture_output=True,text=True);need(cp.returncode==0,'original completed dependency probe')
  generic=[Path(x).resolve()for x in ctx['generic_libraries']]+[Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
  for line in cp.stdout.splitlines():
   p=Path(line).resolve()
   if any(p.is_relative_to(g)for g in generic):continue
   ids=[v for v in maps.values()if v['object'].resolve()==p];need(len(ids)==1 and sha(p)==ids[0]['object_sha256'],'foreign/stale original application edge')
  probes.append({'module':mod,'command':dep,'stdout_sha256':hashlib.sha256(cp.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(cp.stderr.encode()).hexdigest()});maps[mod]={'object':obj,'object_sha256':row['object_sha256']};done.add(mod);ordered.append(row)
 return {'root':str(old),'interrupted_BUILD_sha256':sha(old/'BUILD.json'),'INTERRUPTION_sha256':sha(old/'INTERRUPTION.json'),'TREE_RSS_sha256':sha(old/'TREE_RSS.csv'),'manifest_sha256':sha(old/'SOURCE_CLOSURE.executed.json'),'original_controller_sha256':sha(old/'reproduce.executed.py'),'completed_count':len(ordered),'completed_modules':[x['module']for x in ordered],'dependency_probes':probes},ordered
def copy_reuse(old,out,rows,maps):
 for row in rows:
  mod=row['module'];rel=mod.replace('.','/')
  for directory,suffix in [('source','.lean'),('objects','.olean')]:
   q=out/directory/(rel+suffix);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(old/directory/(rel+suffix),q)
  for suffix in ['stdout','stderr']:shutil.copyfile(old/'logs'/(mod+'.'+suffix),out/'logs'/(mod+'.'+suffix))
  obj=out/'objects'/(rel+'.olean');q=out/'union'/(rel+'.olean');q.parent.mkdir(parents=True,exist_ok=True);need(not q.exists(),'reused namespace collision');q.symlink_to(obj);maps[mod]={'object':obj,'object_sha256':row['object_sha256']}
 return {x['module']:x for x in rows}
