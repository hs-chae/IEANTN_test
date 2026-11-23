#!/usr/bin/env python3
"""Rebuild canonical consumers and entire old-profile glue over fresh316 sources."""
from pathlib import Path
import argparse,importlib.util,os,re,resource,subprocess,time
S=Path(__file__).resolve().parents[1];N=S.parents[1]
spec=importlib.util.spec_from_file_location('resources',S/'scripts/reproduce_pi_resources.py');u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u)
need,sha,read,save,audit=u.need,u.sha,u.read,u.save,u.audit

def validate_spectral(basis,spectral):
 u.validate_basis(basis);m=read(S/'spectral/SOURCE_CLOSURE.json');r=read(spectral/'RESULT.json');b=read(spectral/'BUILD.json')
 need(r['status']=='PASS_COLD261_PLUS_ALL55_SPECTRAL_SOURCES_AND_ACTUAL_CONSUMERS','completed source spectral extension required')
 need(r['basis_RESULT_sha256']==sha(basis/'RESULT.json')and r['basis_BUILD_sha256']==sha(basis/'BUILD.json'),'spectral basis association')
 need(sha(S/'spectral/SOURCE_CLOSURE.json')==r['manifest_sha256']==sha(spectral/'SOURCE_CLOSURE.executed.json'),'spectral manifest')
 need(sha(spectral/'reproduce.executed.py')==r['controller_sha256']==sha(S/'spectral/reproduce_cold_append.py'),'spectral controller')
 cfile=spectral/'C-execution/RESULT.json';need(sha(cfile)==r['coefficient_C_execution_RESULT_sha256'],'C execution receipt binding')
 c=read(cfile);need(c['status']=='PASS_UNCHANGED_SOURCE_FIRST_C_COMPONENT_EXECUTION_JOIN','C execution join')
 need(c['C_source_sha256']==sha(S/'spectral/frozen-source/rh_coeff.c'),'actual coefficient C source identity')
 need(c['formal_model_source_sha256']==sha(spectral/'source/CoefficientPV.lean')and c['formal_proof_stdout_sha256']==sha(spectral/'logs/CoefficientPV.stdout'),'C execution/formal source association')
 need(sha(spectral/'BUILD.json')==r['BUILD_sha256']and b['status']=='PASS','spectral BUILD')
 need(len(b['modules'])==len(m['modules'])==55,'complete spectral55')
 for want,got in zip(m['modules'],b['modules']):
  mod=want['module'];rel=mod.replace('.','/')
  need(got['module']==mod and type(got['returncode'])is int and got['returncode']==0,'spectral compiler status')
  need(sha(N/want['path'])==want['sha256']==got['source_sha256']==sha(spectral/'source'/(rel+'.lean')),'spectral source')
  need(sha(spectral/'objects'/(rel+'.olean'))==got['object_sha256'],'spectral object')
  need(sha(spectral/'logs'/(mod+'.stdout'))==got['stdout_sha256']and sha(spectral/'logs'/(mod+'.stderr'))==got['stderr_sha256'],'spectral logs')
  audit((spectral/'logs'/(mod+'.stdout')).read_text())
 return m,r

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--basis',type=Path,required=True);p.add_argument('--spectral',type=Path,required=True);p.add_argument('--resource-replay',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 basis=a.basis.resolve();spectral=a.spectral.resolve();out=a.out.resolve();base,br=u.validate_basis(basis);sm,sr=validate_spectral(basis,spectral)
 if br.get('resource_complete_default_recipe')is not True:
  need(a.resource_replay is not None,'initial two-stage source run needs explicit independent23resource replay')
  rr=read(a.resource_replay/'RESULT.json');need(rr['status']=='PASS_EXPLICIT_C_RESOURCE_AND_FRESH23_DEPENDENT_PROOF_REPLAY','resource replay incomplete')
  need(sr['resource23_RESULT_sha256']==sha(a.resource_replay/'RESULT.json'),'spectral/resource proof association')
  need(rr['basis_RESULT_sha256']==sha(basis/'RESULT.json')and rr['resource_manifest_sha256']==sha(S/'pi/RESOURCES.json'),'resource replay basis/C association')
  rb=read(a.resource_replay/'BUILD.json');selected=read(S/'pi/RESOURCE_CLOSURE.json')
  need(rr['BUILD_sha256']==sha(a.resource_replay/'BUILD.json')and rb['status']=='PASS','resource replay BUILD')
  need(rr['source_manifest_sha256']==sha(S/'pi/RESOURCE_CLOSURE.json'),'resource source manifest')
  need(len(rb['modules'])==len(selected['modules'])==23 and selected['modules']==base['modules'][238:],'complete23resource replay')
  need(rr['basis_BUILD_sha256']==sha(basis/'BUILD.json'),'resource basis BUILD association')
  need(sha(a.resource_replay/'reproduce.executed.py')==rr['controller_sha256']==sha(S/'scripts/reproduce_pi_resources.py'),'resource controller identity')
  need(rr['default_complete_controller_sha256']==sha(S/'scripts/reproduce_pi_complete.py'),'resource default controller identity')
  for want,row in zip(selected['modules'],rb['modules']):
   mod=want['module'];rel=mod.replace('.','/')
   need(row['module']==mod and type(row['returncode'])is int and row['returncode']==0 and sha(a.resource_replay/'objects'/(rel+'.olean'))==row['object_sha256'],'resource replay object')
   need(sha(N/want['path'])==want['sha256']==row['source_sha256']==sha(a.resource_replay/'source'/(rel+'.lean')),'resource source identity')
   need(sha(a.resource_replay/'logs'/(mod+'.stdout'))==row['stdout_sha256']and sha(a.resource_replay/'logs'/(mod+'.stderr'))==row['stderr_sha256'],'resource logs')
   audit((a.resource_replay/'logs'/(mod+'.stdout')).read_text())
  for payload in read(S/'pi/RESOURCES.json')['resources']:
   need(sha(a.resource_replay/'source'/payload['relative_runtime_path'])==payload['sha256'],'resource C include identity')
 m=read(S/'integration/SOURCE_CLOSURE.json');need(len(m['modules'])==24,'exact final24source extension');done={r['module']for r in base['modules']+sm['modules']}
 for row in m['modules']:
  need(row['module']not in done and set(row['application_imports'])<=done,'canonical source order/identity')
  f=(N/row['path']).resolve();need(f.is_relative_to(S)and sha(f)==row['sha256'],'canonical frozen source')
  if 'original_path'in row:need(sha(N/row['original_path'])==row['sha256'],'current public canonical source drift')
  done.add(row['module'])
 need(not out.exists(),'fresh output required')
 if a.check:print('PASS_COMPLETE_FRESH316_AND_FINAL24_SOURCE_PREFLIGHT');return
 ctx=read(Path(os.environ.get('IEANTN_GENERIC_CONTEXT',N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')));need(sha(ctx['compiler'])==br['compiler_sha256']==ctx['compiler_sha256'],'compiler identity')
 out.mkdir(parents=True);src=out/'source';obj=out/'objects';union=out/'union';logs=out/'logs'
 for d in[src,obj,union,logs]:d.mkdir()
 resource_rows=read(a.resource_replay/'BUILD.json')['modules']if a.resource_replay else[]
 resource_map={x['module']:x for x in resource_rows}
 for bank,rows in [(basis,base['modules']),(spectral,sm['modules'])]:
  for row in rows:
   rel=row['module'].replace('.','/')+'.olean';actual_bank=a.resource_replay if row['module']in resource_map else bank
   q=union/rel;need(not q.exists(),'foundation namespace collision');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(actual_bank/'objects'/rel)
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(union),*ctx['generic_libraries']]);rows=[];audits=[];started=time.monotonic()
 (out/'SOURCE_CLOSURE.executed.json').write_bytes((S/'integration/SOURCE_CLOSURE.json').read_bytes());(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
 for row in m['modules']:
  mod=row['module'];rel=mod.replace('.','/');f=src/(rel+'.lean');f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes((N/row['path']).read_bytes())
  o=obj/(rel+'.olean');o.parent.mkdir(parents=True,exist_ok=True);cmd=[ctx['compiler'],'--root='+str(src),'-j8','-o',str(o),str(f)]
  before=time.monotonic();cp=subprocess.run(['/usr/bin/time','-v',*cmd],cwd=src,env=env,text=True,capture_output=True,preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_AS,(48<<30,48<<30)))
  so=logs/(mod+'.stdout');se=logs/(mod+'.stderr');so.write_text(cp.stdout);se.write_text(cp.stderr)
  row2={'module':mod,'source_sha256':sha(f),'returncode':cp.returncode,'seconds':time.monotonic()-before,'command':['/usr/bin/time','-v',*cmd],'peak_RSS_KiB':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',cp.stderr)[1]),'stdout_sha256':sha(so),'stderr_sha256':sha(se)}
  if cp.returncode==0:row2['object_sha256']=sha(o)
  rows.append(row2);save(out/'BUILD.json',{'status':'RUNNING'if cp.returncode==0 else'FAIL','modules':rows});need(cp.returncode==0,'final consumer compile:'+mod)
  audits+=audit(cp.stdout);q=union/(rel+'.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o);print(len(rows),24,mod,round(row2['seconds'],2),flush=True)
 validate_spectral(basis,spectral);need(set(m['final_roots'])<={x['theorem']for x in audits},'integrated actual theorem audit absent')
 for row in m['modules']:
  need(sha(N/row['path'])==row['sha256'],'canonical source changed')
  if 'original_path'in row:need(sha(N/row['original_path'])==row['sha256'],'public canonical source changed')
 save(out/'BUILD.json',{'status':'PASS','modules':rows})
 result={'status':'PASS_COMPLETE_340_SOURCE_NETWORK_EVOLUTION_CONSUMERS','basis_RESULT_sha256':sha(basis/'RESULT.json'),'spectral_RESULT_sha256':sha(spectral/'RESULT.json'),'resource_replay_RESULT_sha256':sha(a.resource_replay/'RESULT.json')if a.resource_replay else None,'source_manifest_sha256':sha(S/'integration/SOURCE_CLOSURE.json'),'controller_sha256':sha(__file__),'BUILD_sha256':sha(out/'BUILD.json'),'source_modules':340,'canonical_extension_modules':24,'seconds':time.monotonic()-started,'peak_child_RSS_KiB':max(x['peak_RSS_KiB']for x in rows),'owned_final_disk_bytes':sum(x.stat().st_size for x in out.rglob('*')if x.is_file()and not x.is_symlink()),'observed_process_OOM_events':0,'axiom_audits':audits,'entire_previous_Ram_v3_profile_consumed_by_actual_proof':True,'generated_Challenge_scaffolds_imported':False,'historical_application_cache_used':False,'official_Comparator_receipt':False,'whole_pipeline_source_first_PV':False}
 save(out/'RESULT.json',result);print(result['status'],flush=True)
if __name__=='__main__':main()
