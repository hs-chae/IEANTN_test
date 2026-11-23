#!/usr/bin/env python3
"""Independently rebuild all23 C-resource-dependent proofs over the fresh261 run.

This is an explicit supplemental replay after fixing an include-resource omission.
The initial controller and its evidence remain immutable and clearly identified.
The clean default recipe is reproduce_pi_complete.py, which supplies C internally.
"""
from pathlib import Path
import argparse,importlib.util,os,re,resource,subprocess,time
S=Path(__file__).resolve().parents[1];N=S.parents[1]
spec=importlib.util.spec_from_file_location('complete',S/'scripts/reproduce_pi_complete.py');u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u)
need,sha,read,save,audit=u.need,u.sha,u.read,u.save,u.axiom_audit

def validate_basis(basis):
 m=read(S/'pi/SOURCE_CLOSURE.json');r=read(basis/'RESULT.json');b=read(basis/'BUILD.json')
 need(r['status']=='PASS_COLD_ALL_261_SOURCE_MODULES_AND_FINAL_PI_CONSUMERS','complete source basis required')
 need(r['prebuilt_application_objects_used']is False and r['prebuilt_LeanCert_objects_used']is False,'historical proof bank prohibited')
 need(sha(basis/'BUILD.json')==r['BUILD_sha256']and b['status']=='PASS','basis BUILD')
 need(sha(S/'pi/SOURCE_CLOSURE.json')==r['manifest_sha256']==sha(basis/'SOURCE_CLOSURE.executed.json'),'basis manifest')
 need(sha(basis/'reproduce.executed.py')==r['controller_sha256'],'basis controller binding')
 need(len(b['modules'])==len(m['modules'])==261,'complete261source order')
 for want,got in zip(m['modules'],b['modules']):
  mod=want['module'];rel=mod.replace('.','/')
  need(got['module']==mod and type(got['returncode'])is int and got['returncode']==0,'basis actual compiler status')
  need(sha(N/want['path'])==want['sha256']==got['source_sha256']==sha(basis/'source'/(rel+'.lean')),'basis source identity')
  need(sha(basis/'objects'/(rel+'.olean'))==got['object_sha256'],'basis object identity')
  need(sha(basis/'logs'/(mod+'.stdout'))==got['stdout_sha256']and sha(basis/'logs'/(mod+'.stderr'))==got['stderr_sha256'],'basis logs')
  audit((basis/'logs'/(mod+'.stdout')).read_text())
 for payload in u.validate_resources()['resources']:need(sha(basis/'source'/payload['relative_runtime_path'])==payload['sha256'],'actual initial C include bytes')
 return m,r

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--basis',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args();basis=a.basis.resolve();out=a.out.resolve()
 m,r=validate_basis(basis);resource_manifest=u.validate_resources();selected=read(S/'pi/RESOURCE_CLOSURE.json')
 need(len(selected['modules'])==23 and selected['modules']==m['modules'][238:],'exact C-dependent23-source closure')
 need(not out.exists(),'fresh output required')
 if a.check:print('PASS_RESOURCE_BOUND_FRESH261_PREFLIGHT');return
 ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')))
 need(sha(ctx['compiler'])==r['compiler_sha256']==ctx['compiler_sha256'],'compiler identity')
 out.mkdir(parents=True);(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes());src=out/'source';obj=out/'objects';union=out/'union';logs=out/'logs'
 for d in[src,obj,union,logs]:d.mkdir()
 omitted={x['module']for x in selected['modules']}
 for row in m['modules']:
  if row['module']in omitted:continue
  rel=row['module'].replace('.','/')+'.olean';q=union/rel;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(basis/'objects'/rel)
 for payload in resource_manifest['resources']:
  q=src/payload['relative_runtime_path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((N/payload['path']).read_bytes())
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(union),*ctx['generic_libraries']]);rows=[];audits=[];start=time.monotonic()
 for row in selected['modules']:
  mod=row['module'];rel=mod.replace('.','/');f=src/(rel+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes((N/row['path']).read_bytes())
  o=obj/(rel+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
  cmd=[ctx['compiler'],'--root='+str(src),'-j8','-o',str(o),str(f)];before=time.monotonic()
  cp=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=src,env=env,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(48<<30,48<<30)))
  stdout=logs/(mod+'.stdout');stderr=logs/(mod+'.stderr');stdout.write_text(cp.stdout);stderr.write_text(cp.stderr)
  rr={'module':mod,'source_sha256':sha(f),'returncode':cp.returncode,'seconds':time.monotonic()-before,'command':['/usr/bin/time','-v',*cmd],'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',cp.stderr)[1]),'stdout_sha256':sha(stdout),'stderr_sha256':sha(stderr)}
  if cp.returncode==0:rr['object_sha256']=sha(o)
  rows.append(rr);save(out/'BUILD.json',{'status':'RUNNING'if cp.returncode==0 else'FAIL','modules':rows});need(cp.returncode==0,'dependent proof compile:'+mod)
  audits+=audit(cp.stdout);q=union/(rel+'.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o);print(len(rows),23,mod,round(rr['seconds'],2),flush=True)
 need(sha(__file__)==sha(out/'reproduce.executed.py'),'resource replay controller changed')
 validate_basis(basis);need(set(selected['final_roots'])<={x['theorem']for x in audits},'final resource-to-pi consumers absent')
 for payload in resource_manifest['resources']:need(sha(src/payload['relative_runtime_path'])==payload['sha256'],'C payload changed')
 save(out/'BUILD.json',{'status':'PASS','modules':rows})
 result={'status':'PASS_EXPLICIT_C_RESOURCE_AND_FRESH23_DEPENDENT_PROOF_REPLAY','basis_RESULT_sha256':sha(basis/'RESULT.json'),'basis_BUILD_sha256':sha(basis/'BUILD.json'),'resource_manifest_sha256':sha(S/'pi/RESOURCES.json'),'source_manifest_sha256':sha(S/'pi/RESOURCE_CLOSURE.json'),'controller_sha256':sha(__file__),'default_complete_controller_sha256':sha(S/'scripts/reproduce_pi_complete.py'),'BUILD_sha256':sha(out/'BUILD.json'),'source_modules_rebuilt':23,'same_study_fresh_prefix_reused':238,'historical_application_cache_used':False,'seconds':time.monotonic()-start,'peak_child_RSS_KiB':max(x['peak_RSS_KiB']for x in rows),'observed_process_OOM_events':0,'owned_final_disk_bytes':sum(x.stat().st_size for x in out.rglob('*')if x.is_file()and not x.is_symlink()),'axiom_audits':audits,'initial_recipe_self_contained':False,'resource_fix_and_supplemental_replay_explicit':True}
 save(out/'RESULT.json',result);print(result['status'],flush=True)
if __name__=='__main__':main()
