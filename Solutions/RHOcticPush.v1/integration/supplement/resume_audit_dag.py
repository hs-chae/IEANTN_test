"""Reuse exact successful math leaves from a preserved failed-auditor attempt.
The failed original is never promoted or modified; its earlier interruption
origin remains recursively necessary evidence for the reused61 leaves.
"""
from pathlib import Path
import os,subprocess
from resume_dag import need,sha,read,copy_reuse,validate_reuse as old_validate
HERE=Path(__file__).resolve().parent
def validate_reuse(old,m,ctx,primary):
 old=Path(old).resolve();need(not(old/'RESULT.json').exists(),'failed attempt must remain unaccepted')
 need(sha(old/'reproduce.executed.py')==sha(HERE/'resumable.py'),'exact original resumed controller')
 need(sha(old/'SOURCE_CLOSURE.executed.json')==sha(HERE/'capture/SOURCE_CLOSURE.json'),'original failed immutable165 freeze')
 om=read(old/'SOURCE_CLOSURE.executed.json');need(m['original_failed_manifest_sha256']==sha(old/'SOURCE_CLOSURE.executed.json'),'explicit audit-only correction origin')
 need(m['modules'][:-1]==om['modules'][:-1] and m['modules'][-1]['module']==om['modules'][-1]['module']=='FinalSupplementAudit','all164 mathematical sources unchanged')
 b=read(old/'BUILD.json');need(b['status']=='FAIL' and len(b['modules'])==165,'complete failed-audit attempt')
 fail=read(old/'FAILURE.json');need(fail['error']=='supplement compiler failed:FinalSupplementAudit','precise infrastructure failure')
 need(b['modules'][-1]['module']=='FinalSupplementAudit' and b['modules'][-1]['returncode']==1,'only final auditor failed')
 resume=read(old/'RESUME.json')['origin'];origin,previous=old_validate(Path(resume['root']),om,ctx,primary);need(origin==resume,'original interrupted source prefix drift');prior={q['module']:q for q in previous}
 ad=read(old/'RESOURCE_ADMISSION.json');memory=ad['per_job_address_space_cap_bytes'];need(memory==64<<30 and ad['max_parallel_jobs']==6,'preserved run actual resource policy')
 maps=dict(primary);done=set(primary);rows=[];probes=[];roots={}
 for want,row in zip(m['modules'][:-1],b['modules'][:-1]):
  mod=want['module'];need(row['module']==mod and type(row['returncode'])is int and row['returncode']==0,'successful exact164 order')
  need(set(want['application_imports'])<=done,'downward-closed fresh math');rel=mod.replace('.','/');src=old/'source'/(rel+'.lean');obj=old/'objects'/(rel+'.olean')
  need(src.is_file()and obj.is_file()and not src.is_symlink()and not obj.is_symlink(),'owned regular source/object');need(sha(src)==want['sha256']==row['source_sha256']and sha(obj)==row['object_sha256'],'fresh source/object identity')
  cmdroot=Path(origin['root'])if mod in prior else old
  if mod in prior:need(row==prior[mod],'original reused record drift')
  cmd=['/usr/bin/prlimit','--as='+str(memory),'--','/usr/bin/time','-v',ctx['compiler'],'--root='+str(cmdroot/'source'),'-j2','-o',str(cmdroot/'objects'/(rel+'.olean')),str(cmdroot/'source'/(rel+'.lean'))]
  need(row['command']==cmd,'actual original compiler source command');roots[mod]=str(cmdroot)
  for suffix in ['stdout','stderr']:need(sha(old/'logs'/(mod+'.'+suffix))==row[suffix+'_sha256'],'exact original compiler log')
  cmd=[ctx['compiler'],'--root='+str(old/'source'),'--deps',str(src)];env=os.environ.copy();env['LEAN_PATH']=':'.join([str(old/'union'),*ctx['generic_libraries']]);cp=subprocess.run(cmd,cwd=old/'source',env=env,capture_output=True,text=True);need(cp.returncode==0,'actual successful source dependency probe')
  generic=[Path(x).resolve()for x in ctx['generic_libraries']]+[Path(ctx['compiler']).resolve().parent.parent/'lib/lean']
  for line in cp.stdout.splitlines():
   p=Path(line).resolve()
   if any(p.is_relative_to(g)for g in generic):continue
   found=[v for v in maps.values()if v['object'].resolve()==p];need(len(found)==1 and sha(p)==found[0]['object_sha256'],'foreign/stale application dependency')
  import hashlib
  probes.append({'module':mod,'command':cmd,'stdout_sha256':hashlib.sha256(cp.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(cp.stderr.encode()).hexdigest()});maps[mod]={'object':obj,'object_sha256':row['object_sha256']};done.add(mod);rows.append(row)
 return {'root':str(old),'BUILD_sha256':sha(old/'BUILD.json'),'FAILURE_sha256':sha(old/'FAILURE.json'),'TREE_RSS_sha256':sha(old/'TREE_RSS.csv'),'manifest_sha256':sha(old/'SOURCE_CLOSURE.executed.json'),'original_controller_sha256':sha(old/'reproduce.executed.py'),'recursive_interruption_origin':origin,'completed_count':len(rows),'completed_modules':[q['module']for q in rows],'compiler_command_roots':roots,'dependency_probes':probes},rows
