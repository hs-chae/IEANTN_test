"""Offline local coordinator for the Root-reviewed final24 numerical source template.
--check reads only; --prepare-only writes reviewable records; --run authorizes local
resource use and executes complete jobs sequentially through unchanged f16.
"""
from pathlib import Path
from types import SimpleNamespace
import argparse,contextlib,copy,datetime,fcntl,hashlib,importlib.util,io,json,math,os,subprocess,sys
sys.dont_write_bytecode=True
ARCHIVE='1da943a15aaebeb949a5ef472e82e97bb0d349d1914f2f0c01fbfe6f08a1de3a'
CONFIG='d28958255db7d1ff3b2392984935d793baf6541d103840b46d9a2dff11c0fa65'
MANIFEST='59fd529a897cc2f03d1d413a190965d23dc1912b6837381ad1c1895de3ec80fc'
F16='f16b566f7787b98fb132fed7eb6c4e759676e3f6559becee3c71d05bc1dc13bb'
R4E8='4e8a08f643d24b7abcd467c868a3ae923c87ef69908a8d7a04c126b85d815561'
STUDY='ieantn-d01-d02-repair-rerun-20261118'
def need(v,m):
 if not v:raise ValueError(m)
def load(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def finite_float(value):
  result=float(value);need(math.isfinite(result),'nonfinite JSON float overflow');return result
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_float=finite_float,parse_constant=lambda s:(_ for _ in()).throw(ValueError(s)))
def pin(p):p=Path(p).resolve();return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def write(p,v):
 need(not p.exists(),'never overwrite '+str(p));tmp=p.with_name(p.name+'.pending');need(not tmp.exists(),'preserve partial metadata');tmp.write_text(json.dumps(v,sort_keys=True,indent=2,allow_nan=False)+'\n');os.link(tmp,p);tmp.unlink();return pin(p)
def module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def cli(argv):
 need(argv[1:3]==['-I','-B']and argv[-1]=='--check','metadata-only original CLI')
 m=module('exact_unchanged_f16_metadata_check',Path(argv[3]));saved=list(sys.argv);stream=io.StringIO()
 try:
  sys.argv=[argv[3]]+argv[4:]
  with contextlib.redirect_stdout(stream):m.main()
 finally:sys.argv=saved
 v=json.loads(stream.getvalue());need(v['scope_calls']==v['model_calls']==0,'metadata only');return v

def verify_prepared(auth,commands,deps,delegation_pin,root,registry):
 plan=load(auth/'PREPARED_PIPELINE.json');need(plan['source_root']==str(root)and plan['registry']==str(registry)and plan['delegation']==delegation_pin and plan['source_pins']==deps and plan['cases']==[x['candidate_id']for x in commands]and plan['commands']==commands,'exact prepared pipeline binding');sp=plan['source_approval'];need(pin(auth/'SOURCE_APPROVAL.json')==sp,'prepared source approval pin');source=load(sp['path']);need(source['schema']=='ROOT_PORTABLE_NUMERICAL_EXECUTOR_SOURCE_V1'and source['status']=='ROOT_APPROVED_PORTABLE_NUMERICAL_EXECUTOR_SOURCE'and source['reviewed_by']=='/root'and source['source_pins']==deps and source['source_root']==str(root)and source['resource_registry_root']==str(registry)and source['delegated_authority_template']==delegation_pin and source['authority_issuer']=='LOCAL_OPERATOR_USING_ROOT_REVIEWED_SOURCE_TEMPLATE'and source['new_Root_math_or_source_review_performed']is False,'exact delegated prepared source approval binding');records=plan['prepared_records'];need(len(records)==len(commands)and len({x['candidate_id']for x in records})==len(commands),'every unique prepared record pin')
 for row in commands:
  cid=row['candidate_id'];record=next(x for x in records if x['candidate_id']==cid);jp=auth/(cid+'.JOB_ROOT.json');ep=auth/(cid+'.EXECUTION_ROOT.json');need(pin(jp)==record['job']and pin(ep)==record['execution'],'prepared job and execution pins');baseline=load(row['original_job']['path']);need(pin(row['original_job']['path'])==row['original_job'],'exact frozen baseline');job=load(jp);normalized=copy.deepcopy(job)
  for key in ['status','reviewed_by','registered_executor_selection']:normalized[key]=baseline[key]
  need(normalized==baseline,'prepared mathematical job differs from exact frozen baseline; only three authority fields may change');need(job['status']=='ROOT_REVIEWED_NO_MODEL_REPRODUCTION'and job['reviewed_by']=='/root'and job['registered_executor_selection']=={'status':'ROOT_REVIEWED_EXISTING_REGISTERED_NO_MODEL_EXECUTOR','authority_pin':sp},'prepared job authority fields bound');execution=load(ep)
  need(execution['schema']=='ROOT_ONE_PORTABLE_NUMERICAL_REPRODUCTION_V1'and execution['status']=='ROOT_APPROVED_EXACT_NO_MODEL_NUMERICAL_REPRODUCTION'and execution['reviewed_by']=='/root'and execution['candidate_id']==cid and execution['job']==pin(jp)and execution['source_approval']==sp and execution['source_pins']==deps and execution['approved_out']==row['out']and execution['approved_resource_out']==row['resource_out']and execution['resource_registry_root']==str(registry)and type(execution['model_calls'])is int and execution['model_calls']==0 and execution['delegated_authority_template']==delegation_pin and execution['authority_issuer']=='LOCAL_OPERATOR_USING_ROOT_REVIEWED_SOURCE_TEMPLATE','exact prepared execution/source/job/output binding');cli(row['argv_run'][:-1]+['--check'])
 return plan

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--source-root',type=Path,required=True);p.add_argument('--registry',type=Path,required=True);p.add_argument('--authority-dir',type=Path,required=True);p.add_argument('--delegation',type=Path);p.add_argument('--cases',default='all');modes=p.add_mutually_exclusive_group(required=True);modes.add_argument('--check',action='store_true');modes.add_argument('--prepare-only',action='store_true');modes.add_argument('--run',action='store_true');a=p.parse_args();root=a.source_root.resolve();study=root/STUDY;config=root/'portable/RELOCATION_CONFIG.json';manifest=root/'portable/EXACT_SOURCE_MANIFEST.json';helper=study/'scripts/portable_relocation_metadata_v2.py';adapter=study/'scripts/run_portable_numerical_reproduction_relocated_v2.py';auth=a.authority_dir.resolve();need(not auth.is_relative_to(root),'authority records outside frozen source');need(pin(config)['sha256']==CONFIG and pin(manifest)['sha256']==MANIFEST and pin(helper)['sha256']==R4E8 and pin(adapter)['sha256']==F16,'exact final24 immutable source/config/executors');r=module('existing_final24_relocation',helper).Relocation(root,config);registry=r.registry(a.registry)
 expected=set(r.files)|{'portable/EXACT_SOURCE_MANIFEST.json','portable/RELOCATION_CONFIG.json','portable/BUILD_RECEIPT.json'};need(len(expected)==7303 and {str(x.relative_to(root))for x in root.rglob('*')if x.is_file()}==expected,'fresh exact7303-member source tree; use fresh extraction for a new invocation');cases={x['candidate_id']:x for x in r.collection['cases']};need(len(cases)==24 and not r.collection['pending_cases'],'complete24 frozen cases');ids=sorted(cases)if a.cases=='all'else a.cases.split(',');need(ids and len(set(ids))==len(ids)and all(x in cases for x in ids),'exact unique canonical cases or all')
 delegation=None
 if a.delegation:
  delegation=load(a.delegation);need(delegation['schema']=='ROOT_DELEGATED_FINAL24_LOCAL_REPRODUCTION_TEMPLATE_V1'and delegation['status']=='ROOT_APPROVED_BOUNDED_LOCAL_NUMERICAL_REPRODUCTION_COORDINATOR'and delegation['reviewed_by']=='/root','Root-reviewed bounded local template required');need(delegation['coordinator_sha256']==pin(Path(__file__))['sha256']and delegation['archive_sha256']==ARCHIVE and delegation['config_sha256']==CONFIG and delegation['manifest_sha256']==MANIFEST,'exact coordinator/template source identity');need(delegation['maximum_numerical_jobs']==2 and delegation['maximum_all_pending_registered']==6 and delegation['no_mathematical_or_core_changes']is True,'unchanged delegation bounds');original=a.delegation.parent/delegation['original_Root_source_approval_copy'];need(pin(original)['sha256']==delegation['original_Root_source_approval_sha256'],'preserved original Root source-review provenance')
 need(a.check or delegation is not None,'--prepare-only/--run need the shipped Root template delegation, no manual JSON editing');need(not auth.exists()or(auth.is_dir()and(auth/'PREPARED_PIPELINE.json').is_file()),'fresh authority dir or exact existing prepared plan only');commands=[];deps=None
 for cid in ids:
  original=r.checked(cases[cid]['job_plan']);job=load(original);out=study/'evidence/portable-relocated-reproduction-v2'/cid;res=study/'resources/portable-relocated-reproduction-v2'/cid;need(not out.exists()and not res.exists(),'fresh case outputs; preserve previous attempts');common=[sys.executable,'-I','-B',str(adapter),'--source-root',str(root),'--relocation-config',str(config),'--resource-registry-root',str(registry),'--out',str(out),'--resource-out',str(res)];check=common+['--job',str(original),'--check'];v=cli(check)
  if deps is None:deps=v['source_pins']
  need(v['source_pins']==deps,'same source dependency closure');commands.append({'candidate_id':cid,'original_job':pin(original),'out':str(out),'resource_out':str(res),'argv_run':common+['--job',str(auth/(cid+'.JOB_ROOT.json')),'--root-authorization',str(auth/(cid+'.EXECUTION_ROOT.json')),'--run']})
 if a.check:
  if auth.exists():
   need(delegation is not None,'provide shipped template to check prepared records');verify_prepared(auth,commands,deps,pin(a.delegation),root,registry)
  print(json.dumps({'status':'PASS_FINAL24_LOCAL_COORDINATOR_METADATA_ONLY','cases':ids,'full_case_route_counts':{cid:load(r.checked(cases[cid]['job_plan']))['complete_active_cli_and_compile_route_count']for cid in ids},'exact_archive_sha256':ARCHIVE,'actual_scopes_compilers_models':0,'delegation_present':delegation is not None,'prepared_records_rechecked':auth.exists()},sort_keys=True));return
 now=datetime.datetime.now(datetime.timezone.utc).isoformat();delegation_pin=pin(a.delegation)
 if not auth.exists():
  need(auth.parent.is_dir(),'authority parent must exist');auth.mkdir(mode=0o700);source={'schema':'ROOT_PORTABLE_NUMERICAL_EXECUTOR_SOURCE_V1','status':'ROOT_APPROVED_PORTABLE_NUMERICAL_EXECUTOR_SOURCE','reviewed_by':'/root','source_pins':deps,'source_root':str(root),'resource_registry_root':str(registry),'delegated_authority_template':delegation_pin,'authority_issuer':'LOCAL_OPERATOR_USING_ROOT_REVIEWED_SOURCE_TEMPLATE','issued_at_utc':now,'new_Root_math_or_source_review_performed':False,'source_first_PV':False,'full_analytic_Lean':False};sp=write(auth/'SOURCE_APPROVAL.json',source)
  records=[]
  for row in commands:
   cid=row['candidate_id'];job=copy.deepcopy(load(row['original_job']['path']));job.update(status='ROOT_REVIEWED_NO_MODEL_REPRODUCTION',reviewed_by='/root',registered_executor_selection={'status':'ROOT_REVIEWED_EXISTING_REGISTERED_NO_MODEL_EXECUTOR','authority_pin':sp});jp=write(auth/(cid+'.JOB_ROOT.json'),job);execution={'schema':'ROOT_ONE_PORTABLE_NUMERICAL_REPRODUCTION_V1','status':'ROOT_APPROVED_EXACT_NO_MODEL_NUMERICAL_REPRODUCTION','reviewed_by':'/root','candidate_id':cid,'job':jp,'source_approval':sp,'source_pins':deps,'approved_out':row['out'],'approved_resource_out':row['resource_out'],'resource_registry_root':str(registry),'model_calls':0,'no_research_wall_token_operation_cap':True,'source_first_PV':False,'full_analytic_Lean':False,'delegated_authority_template':delegation_pin,'authority_issuer':'LOCAL_OPERATOR_USING_ROOT_REVIEWED_SOURCE_TEMPLATE','operator_must_explicitly_pass_run_before_scientific_execution':True};ep=write(auth/(cid+'.EXECUTION_ROOT.json'),execution);records.append({'candidate_id':cid,'job':jp,'execution':ep});cli(row['argv_run'][:-1]+['--check'])
  write(auth/'PREPARED_PIPELINE.json',{'schema':'FINAL24_REVIEWABLE_LOCAL_NUMERICAL_PIPELINE_V1','source_root':str(root),'registry':str(registry),'delegation':delegation_pin,'source_pins':deps,'cases':ids,'commands':commands,'source_approval':sp,'prepared_records':records,'maximum_concurrent_jobs_in_this_coordinator':1,'numerical_executions_during_preparation':0})
 plan=verify_prepared(auth,commands,deps,delegation_pin,root,registry)
 if a.prepare_only:print(json.dumps({'status':'PREPARED_REVIEWABLE_LOCAL_RECORDS_NO_SCIENCE','pipeline':pin(auth/'PREPARED_PIPELINE.json'),'cases':ids,'scopes_compilers_models':0}));return
 # --run is the local operator's explicit authorization for this fresh pipeline.
 registry.mkdir(parents=True,exist_ok=True);lock=(registry/'final24-coordinator.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);done=[]
 for row in commands:
  # Reuse the existing registry lock for a consistent read. It must be
  # released before f16 reserves under its own exclusive lock; therefore
  # numerical2 is a dispatch precheck, not a cross-controller atomic claim.
  with(registry/'allocations.lock').open('a')as admission:
   fcntl.flock(admission,fcntl.LOCK_SH);allocations=load(registry/'allocations.json')['allocations']if(registry/'allocations.json').exists()else[]
  need(len(allocations)<6 and sum('NUMERICAL_REPRODUCTION'in x['run']for x in allocations)<2,'observed global6/numerical2 admission; use one trusted host dispatcher and retain unstarted plan until a genuine free window');cid=row['candidate_id'];inv=auth/(cid+'.ACTUAL_INVOCATION.json');write(inv,{'argv':row['argv_run'],'local_operator_explicit_run':True,'delegation':delegation_pin,'actual_model_calls':0});code=subprocess.run(row['argv_run']).returncode;need(code==0,'actual full numerical run failed/interrupted: preserve all evidence; never overwrite or auto-rerun')
  out=Path(row['out']);resdir=Path(row['resource_out']);fp=out/'FINAL_REPRODUCTION_RECEIPT.json';final=load(fp);res=load(resdir/'RECEIPT.json');need(final['status']=='PASS_EXACT_NUMERICAL_REPRODUCTION_AND_ACTUAL_DRAIN'and final['execution_drained']is True and final['reservation_released']is True and res['returncode']==0 and res['error']is None and res['execution_drained']is True and res['reservation_released']is True,'actual complete outputs/resource0/drain/release required');unit=res['reservation']['unit'];q=subprocess.run(['systemctl','--user','show',unit,'--property=MainPID','--property=ActiveState'],capture_output=True,text=True);state=dict(x.split('=',1)for x in q.stdout.splitlines()if'='in x);need(state.get('MainPID')=='0'and state.get('ActiveState')=='inactive'and not(Path('/sys/fs/cgroup')/res['reservation']['cgroup'].lstrip('/')).exists(),'actual unit and cgroup drained');need(not any(x['run']==res['reservation']['run']for x in load(registry/'allocations.json')['allocations']),'exact lease absent');m=module('unchanged_completed_final24_f16',adapter);args=SimpleNamespace(source_root=root,relocation_config=config,resource_registry_root=registry,out=out,resource_out=resdir);m.configure_relocation(args);wrapper,_=m.sources();np=m.verify_outputs(args,load(auth/(cid+'.JOB_ROOT.json')),wrapper);need(pin(np)==final['numerical_receipt'],'independent exact complete output verification');done.append({'candidate_id':cid,'final_receipt':pin(fp),'resource_receipt':pin(resdir/'RECEIPT.json'),'all_full_numerical_outputs_verified':True,'actual_inactive_PID0':state,'cgroup_and_lease_absent':True});write(auth/(cid+'.ACTUAL_COMPLETE_READBACK.json'),done[-1])
 write(auth/'ACTUAL_PIPELINE_COMPLETE.json',{'status':'ALL_SELECTED_FULL_NUMERICAL_JOBS_ACTUALLY_COMPLETED_OUTPUTS_VERIFIED_AND_DRAINED','cases':done,'model_calls':0,'source_first_PV':False,'full_analytic_Lean':False,'deletions':0});print(json.dumps({'status':'ACTUAL_SELECTED_NUMERICAL_PIPELINE_COMPLETE','cases':ids,'receipt':pin(auth/'ACTUAL_PIPELINE_COMPLETE.json')}))
if __name__=='__main__':main()
