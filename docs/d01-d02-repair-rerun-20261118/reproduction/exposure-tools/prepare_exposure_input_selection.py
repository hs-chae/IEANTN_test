"""Preserve exact public scientific task/treatment input metadata, no new research."""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,json
A=Path(__file__).resolve().parent;R=A.parents[1];OLD=R.parent/'ieantn-deep-tertiary-exposure-a-20261117'
sp=importlib.util.spec_from_file_location('source_inventory',A/'prepare_inventory.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--snapshot',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);q=ap.parse_args();m.need(not q.out.exists(),'fresh exposure input selection');x=m.load(q.snapshot);selected={};runtime_paths=set();actual=[]
 def add(p,dest,category):
  p=Path(p);m.need(p.is_file() and not p.is_symlink(),'exact public scientific input file');b=p.read_bytes();inspection=m.inspect_bytes(p.name,b)
  if p.name.endswith('.json.gz'):
   inner=gzip.decompress(b);sub=m.inspect_bytes(p.name[:-3],inner);inspection['decompressed_exact_JSON_payload']={'sha256':hashlib.sha256(inner).hexdigest(),'bytes':len(inner),'inspection':sub};inspection['flags']+=sub['flags']
  m.need(not inspection['flags'],'actual public-input schema/member scan requires Root review before selection')
  row={'path':str(p.resolve()),'sha256':sha(p),'bytes':len(b),'archive_path':dest,'gzip_json':p.suffix=='.json' and len(b)>=65536,'category':category,'actual_schema_and_payload_inspection':inspection}
  if dest in selected:m.need(selected[dest]['sha256']==row['sha256'],'input destination collision')
  selected[dest]=row
 for name in ['reproduce_baselines.py','baseline_reproduction_pins.json.gz','reproduce_full_generic_cache.py','prepare_ieantn_generic_runtime_v2.py']:
  add(OLD/'scripts'/name,'reproduction/exposure-tools/'+name,'HISTORICAL_PINNED_BASELINE_SOURCE_REBUILD_RECIPE_NOT_NEW_COLD_EXECUTION')
 for arm in ['PNT','IEANTN_GENERIC_COMPLETE_V2','NL']:runtime_paths.add(OLD/'protocol/runtimes'/arm/'runtime.json')
 generic_names={'COMMON_FOUNDATION.md','BASELINES.md','EVALUATION_RULES.md','CHECKPOINTS.md','OPERATING_NOTICES.md','INPUT_CONTRACT.json','SOURCE_INDEX.json','RUNTIME_PATHS.json','BUDGET.json'}
 # Preserve every actual research/review packet manifest; content selection below is explicit.
 for stage in x['stages']:
  for phase in ['research_physical_results','review_physical_results']:
   for result in stage[phase]:
    ref=result['source'];rp=R/ref['study_relative_path'] if 'study_relative_path'in ref else R.parent/ref['workspace_relative_path'];m.need(sha(rp)==ref['sha256'],'actual physical result metadata');z=m.load(rp);limits=z['limits'];mp=Path(limits['packet_manifest']);manifest=m.load(mp);folder=Path(limits['packet']);m.need(mp.is_relative_to(R) and folder.is_relative_to(R),'owned recorded scientific packet');add(mp,'experiment-inputs/study/'+str(mp.relative_to(R)),'ACTUAL_RECORDED_MODEL_PACKET_MANIFEST_SOURCE_IDENTITY')
    runtime_paths.add(Path(limits['runtime']));included=[]
    for f in manifest['files']:
     p=folder/f['path'];m.need(sha(p)==f['sha256'],'every actual recorded packet payload hash')
     if f['path']in generic_names:
      add(p,'experiment-inputs/study/'+str(p.relative_to(R)),'EXPLICIT_PUBLIC_GENERIC_MATHEMATICAL_TASK_AND_PARAMETER_INPUT');included.append(f['path'])
    actual.append({'candidate_id':stage['candidate_id'],'phase':phase,'result_sha256':ref['sha256'],'packet_manifest':{'path':str(mp),'sha256':sha(mp)},'runtime':{'path':str(limits['runtime']),'sha256':sha(limits['runtime'])},'explicit_generic_files_preserved':included,'private_or_own_specific_task_context_not_exported_by_this_selection':True})
 # Only the genuinely common fresh-worker task is exported; no combined coordinator prompt.
 first=R/'protocol/packets-first-fresh-D01-v3';task_bytes=[];actual_manifest_paths={z['packet_manifest']['path']for z in actual}
 for folder in sorted(p for p in first.iterdir()if p.is_dir()):
  p=folder/'TASK.md';m.need(str(first/(folder.name+'.manifest.json')) in actual_manifest_paths,'common TASK belongs to actual recorded research run, not preparation');m.need(p.is_file(),'actual first fresh task');task_bytes.append(p.read_bytes());add(p,'experiment-inputs/study/'+str(p.relative_to(R)),'ACTUAL_COMMON_FRESH_RESEARCH_TASK_PUBLIC_SCIENTIFIC_INPUT')
 m.need(len(task_bytes)==3 and len(set(task_bytes))==1,'first three actual fresh tasks byte-identical')
 add(R/'scripts/build_research_packets.py','experiment-inputs/study/scripts/build_research_packets.py','PUBLIC_GENERIC_COMMON_TASK_AND_SOURCE_POLICY_BUILDER')
 for rp in sorted(runtime_paths):
  d=m.load(rp);m.need(d.get('external_network')is False and d.get('host_tools')is False,'recorded research/review runtime network/tool boundary');add(rp,'experiment-inputs/legacy-study/'+str(rp.relative_to(OLD)),'ACTUAL_RESEARCH_OR_REVIEW_SOURCE_AND_COMPILER_CONTEXT_DESCRIPTOR')
  for row in d['mounts']:
   z=row['manifest'];p=m.readpin(z);add(p,'experiment-inputs/legacy-study/'+str(p.relative_to(OLD)),'EXACT_HASHED_EXPOSURE_SOURCE_OR_GENERIC_OBJECT_TREE_MANIFEST_NOT_CACHE_PAYLOAD')
  if d.get('native_closure_audit'):
   p=m.readpin(d['native_closure_audit']);add(p,'experiment-inputs/legacy-study/'+str(p.relative_to(OLD)),'EXACT_NATIVE_EXPOSURE_CLOSURE_SOURCE_AUDIT')
 result={'status':'PUBLIC_SCIENTIFIC_EXPOSURE_INPUTS_CURRENT_BYTE_AND_SCHEMA_PRESERVATION_ONLY','actual_physical_results':actual,'assets':sorted(selected.values(),key=lambda z:z['archive_path']),'asset_count':len(selected),'bytes':sum(z['bytes']for z in selected.values()),'new_research_review_cold_Lean_or_model_runs':0,'historical_baseline_rebuild_recipe_is_not_claimed_reexecuted_now':True,'stochastic_rediscovery_not_promised':True,'raw_private_coordinator_prompts_native_events_reasoning_auth_installed_caches_exported':False,'source_code':{'path':str(Path(__file__)),'sha256':sha(Path(__file__))}}
 with q.out.open('x')as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
 print(json.dumps({'status':result['status'],'assets':len(selected),'bytes':result['bytes'],'actual_result_records':len(actual),'runtime_descriptors':len(runtime_paths),'sha256':sha(q.out)},sort_keys=True))
if __name__=='__main__':main()
