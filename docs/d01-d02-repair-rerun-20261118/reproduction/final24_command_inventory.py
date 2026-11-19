"""Read/hash the exact final24 source tree and print every replay command; never execute science."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
ARCHIVE_SHA='1da943a15aaebeb949a5ef472e82e97bb0d349d1914f2f0c01fbfe6f08a1de3a'
CONFIG_SHA='d28958255db7d1ff3b2392984935d793baf6541d103840b46d9a2dff11c0fa65'
MANIFEST_SHA='59fd529a897cc2f03d1d413a190965d23dc1912b6837381ad1c1895de3ec80fc'
HELPER_SHA='4e8a08f643d24b7abcd467c868a3ae923c87ef69908a8d7a04c126b85d815561'
ADAPTER_SHA='f16b566f7787b98fb132fed7eb6c4e759676e3f6559becee3c71d05bc1dc13bb'
STUDY='ieantn-d01-d02-repair-rerun-20261118'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(p):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError(x)))
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--source-root',type=Path,required=True);p.add_argument('--registry',type=Path,required=True);p.add_argument('--controller-python',default='python3');p.add_argument('--new-authority-directory',type=Path,required=True);a=p.parse_args();root=a.source_root.resolve();study=root/STUDY;config=root/'portable/RELOCATION_CONFIG.json';manifest=root/'portable/EXACT_SOURCE_MANIFEST.json';helper=study/'scripts/portable_relocation_metadata_v2.py';adapter=study/'scripts/run_portable_numerical_reproduction_relocated_v2.py'
 need(sha(config)==CONFIG_SHA and sha(manifest)==MANIFEST_SHA and sha(helper)==HELPER_SHA and sha(adapter)==ADAPTER_SHA,'exact final24 source/config/manifest/frozen executors')
 spec=importlib.util.spec_from_file_location('final24_existing_relocation_metadata_only',helper);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);r=m.Relocation(root,config);registry=r.registry(a.registry);cases=r.collection['cases'];need(len(cases)==24 and {x['candidate_id']for x in cases}=={'FOLLOWUP-C'+str(i).zfill(3)for i in range(1,25)}and not r.collection['pending_cases'],'exact complete24 source route population');authority=a.new_authority_directory.resolve();need(not authority.is_relative_to(root),'new authority must remain outside immutable source manifest')
 rows=[]
 for entry in sorted(cases,key=lambda x:x['candidate_id']):
  cid=entry['candidate_id'];job=r.checked(entry['job_plan']);v=load(job);need(v['candidate_id']==cid,'one exact case identity');out=study/'evidence/portable-relocated-reproduction-v2'/cid;res=study/'resources/portable-relocated-reproduction-v2'/cid;common=[a.controller_python,'-I','-B',str(adapter),'--source-root',str(root),'--relocation-config',str(config),'--resource-registry-root',str(registry),'--out',str(out),'--resource-out',str(res)];check=common+['--job',str(job),'--check'];run=common+['--job',str(authority/(cid+'.JOB_ROOT.json')),'--root-authorization',str(authority/(cid+'.EXECUTION_ROOT.json')),'--run']
  rows.append({'candidate_id':cid,'stage_id':v['stage_id'],'source_job':{'path':str(job),'sha256':sha(job)},'literal_source_metadata_check_argv':check,'literal_run_argv_requires_new_exact_coordinator_authorities':run,'top_level_original_routes':v['jobs'],'nested_original_routes':v['nested_active_child_routes'],'complete_route_count':v['complete_active_cli_and_compile_route_count'],'original_source_assets':v['source_assets'],'exact_parameters':v['exact_parameters'],'precise_scope_notes':v['precise_notes'],'new_replay_executed_by_inventory':False})
 result={'schema':'FINAL24_EXACT_SOURCE_AND_COMMAND_INVENTORY_NO_EXECUTION_V1','status':'ALL24_SOURCE_HASHES_CHECKED_COMMANDS_EMITTED_NO_SCIENCE_RUN','archive_sha256':ARCHIVE_SHA,'source_manifest_sha256':MANIFEST_SHA,'source_root':str(root),'source_files':len(r.files),'archive_regular_members':len(r.files)+3,'cases':rows,'all24_source_coverage_not_a_claim_of_new24_replays_here':True,'new_source_job_execution_authorities_required_for_every_fresh_tree':True,'maximum_numerical_jobs':2,'maximum_all_pending_plus_registered':6,'scopes_compilers_numerical_or_model_calls':0,'source_first_PV':False,'full_analytic_Lean':False}
 print(json.dumps(result,sort_keys=True,indent=2,allow_nan=False))
if __name__=='__main__':main()
