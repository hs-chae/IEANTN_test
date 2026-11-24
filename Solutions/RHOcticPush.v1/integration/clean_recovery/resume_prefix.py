"""Admit only the exact source-fresh prefix of a failed clean primary replay.
This does not accept that run. Its prerequisite failure, exact sources and all logs remain unchanged.
"""
from pathlib import Path
import hashlib,json,subprocess,shutil
HERE=Path(__file__).resolve().parent;I=HERE.parent;R=I.parents[2]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def validate_prefix(old,m,ctx,foundation):
 old=Path(old).resolve();need((old/'FAILURE.json').is_file()and not(old/'RESULT.json').exists(),'only completed rejected original attempt may supply prefix')
 need(sha(old/'reproduce.executed.py')==sha(I/'clean_recovery/ORIGINAL_PRIMARY_CONTROLLER.py'),'original executed controller pin')
 need(sha(old/'SOURCE_CLOSURE.executed.json')==sha(I/'corrected/capture/SOURCE_CLOSURE.json'),'original failed source freeze pin')
 orig=read(old/'SOURCE_CLOSURE.executed.json');b=read(old/'BUILD.json');need(b['status']=='FAIL','original prerequisite-failed attempt must remain rejected')
 need(len(b['modules'])==81 and type(b['modules'][-1]['returncode'])is int and b['modules'][-1]['returncode']==1,'precise failed final compiler status')
 failed=b['modules'][-1];need(failed['module']=='OcticQuadrature','fixed missing-prerequisite failure identity')
 failed_source=old/'source/OcticQuadrature.lean'
 need(failed_source.is_file()and not failed_source.is_symlink(),'original failed source retained')
 need(orig['modules'][80]['module']=='OcticQuadrature'and
      sha(failed_source)==failed['source_sha256']==orig['modules'][80]['sha256']==m['modules'][80]['sha256'],
      'failed source exact snapshot/capture identity')
 need(failed['command']==['/usr/bin/time','-v',ctx['compiler'],'--root='+str(old/'source'),'-j4',
      '-o',str(old/'objects/OcticQuadrature.olean'),str(failed_source)],'failed command preserved')
 need('Mathlib/Combinatorics/SimpleGraph/Walk/Subwalks.olean' in (old/'logs/OcticQuadrature.stdout').read_text(),'actual missing generic prerequisite evidence')
 for suff in ['stdout','stderr']:need(sha(old/'logs'/('OcticQuadrature.'+suff))==failed[suff+'_sha256'],'failed prerequisite logs preserved')
 need(read(old/'RESOURCE_ADMISSION.json')['memory_cap_bytes']==128<<30,'original resource policy')
 maps=dict(foundation);prefix=[];probes=[]
 for index,row in enumerate(b['modules']):
  if type(row['returncode'])is not int or row['returncode']!=0:break
  want=m['modules'][index];prior=orig['modules'][index];mod=want['module'];rel=mod.replace('.','/');need(mod==row['module']==prior['module'],'contiguous prefix identity')
  if want['sha256']!=prior['sha256']:break
  source=old/'source'/(rel+'.lean');obj=old/'objects'/(rel+'.olean');need(source.is_file()and obj.is_file()and not source.is_symlink()and not obj.is_symlink(),'owned original source/object')
  need(sha(source)==want['sha256']==row['source_sha256']and sha(obj)==row['object_sha256'],'prefix exact source/object')
  cmd=['/usr/bin/time','-v',ctx['compiler'],'--root='+str(old/'source'),'-j4','-o',str(obj),str(source)];need(row['command']==cmd,'prefix compiler command')
  for suff in ['stdout','stderr']:need(sha(old/'logs'/(mod+'.'+suff))==row[suff+'_sha256'],'prefix compiler log')
  # Probe against only the actual run union and pinned generic banks. Each
  # application edge must terminate in the same fresh foundation or prior prefix.
  env=__import__('os').environ.copy();env['LEAN_PATH']=':'.join([str(old/'union'),*ctx['generic_libraries']]);dep=[ctx['compiler'],'--root='+str(old/'source'),'--deps',str(source)];cp=subprocess.run(dep,cwd=old/'source',env=env,capture_output=True,text=True);need(cp.returncode==0,'prefix dependency probe')
  need(bool(cp.stdout.strip()),'actual prefix dependency probe must not be empty')
  generic=[Path(x).resolve()for x in ctx['generic_libraries']]+[Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
  for line in cp.stdout.splitlines():
   f=Path(line).resolve()
   if any(f.is_relative_to(p)for p in generic):continue
   ids=[v for v in maps.values()if v['object'].resolve()==f];need(len(ids)==1 and sha(f)==ids[0]['object_sha256'],'prefix foreign/stale application edge')
  probes.append({'module':mod,'command':dep,'stdout_sha256':hashlib.sha256(cp.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(cp.stderr.encode()).hexdigest()});maps[mod]={'object':obj,'object_sha256':row['object_sha256']};prefix.append(row)
 need(len(prefix)==80,'all80 exact clean-source prefix modules required')
 receipt={'root':str(old),'rejected_BUILD_sha256':sha(old/'BUILD.json'),'rejected_FAILURE_sha256':sha(old/'FAILURE.json'),'original_controller_sha256':sha(old/'reproduce.executed.py'),'original_manifest_sha256':sha(old/'SOURCE_CLOSURE.executed.json'),'prefix_count':len(prefix),'prefix_compiler_seconds':sum(x['seconds']for x in prefix),'first_recompiled_module':m['modules'][len(prefix)]['module'],'original_failure_kind':'missing pinned generic object, not mathematical proof failure or OOM','prefix_dependency_probes':probes}
 return receipt,prefix
def copy_prefix(old,out,rows,union,maps):
 for row in rows:
  mod=row['module'];rel=mod.replace('.','/')
  for directory,suffix in [('source','.lean'),('objects','.olean')]:
   dest=out/directory/(rel+suffix);dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(old/directory/(rel+suffix),dest)
  for suff in ['stdout','stderr']:shutil.copyfile(old/'logs'/(mod+'.'+suff),out/'logs'/(mod+'.'+suff))
  obj=out/'objects'/(rel+'.olean');q=union/(rel+'.olean');q.parent.mkdir(parents=True,exist_ok=True);need(not q.exists(),'prefix namespace collision');q.symlink_to(obj);maps[mod]={'object':obj,'object_sha256':row['object_sha256']}
 return list(rows)
