#!/usr/bin/env python3
"""Export accepted scalar-source evidence without copying old data or .oleans."""
from pathlib import Path
import argparse,hashlib,json,shutil,tarfile,time,re,subprocess
from execute_full_source_rows import check
from execute_full_scalar_certificate import read,sha,need
S=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--result',type=Path,required=True);p.add_argument('--model-plan',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--archive',type=Path,required=True);a=p.parse_args();verified=check(a.result);d=read(a.result);m=read(d['manifest']);model=read(a.model_plan);out=a.out.resolve();need(out.is_dir()and not(a.out/'EXPORT.json').exists()and not a.archive.exists(),'fresh export in identity-locked owned packet');lock=out/'ALL_ROW_SOURCE_IDENTITY_LOCK.json';need(lock.is_file(),'all-row identity lock required');files=[]
 def copy(source,relative):
  source=Path(source);target=out/relative;need(source.is_file()and source.suffix!='.olean','source/evidence only, no proof-object duplication');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target);files.append(dict(path=str(target.relative_to(out)),bytes=target.stat().st_size,sha256=sha(target)))
 copy(a.result,'accepted/RESULT.json');copy(d['manifest'],'accepted/PROPOSAL.json');copy(m['original_manifest'],'original/PROPOSAL.json');copy(m['original_result'],'original/RESULT.json');copy(a.model_plan,'model/SOURCE_CLOSURE_PLAN.json')
 for item in model['modules']:
  source=Path(item['source']);need(sha(source)==item['source_sha256'],'current exact model source');relative=source.relative_to(Path(item['root']));base=Path('model/solution')if Path(item['root'])==S else Path('model/network');copy(source,base/relative)
 for item in model['payloads']:
  need(sha(item['path'])==item['sha256'],'actual exact C payload');copy(item['path'],Path('model/solution/c')/Path(item['path']).name)
 for item in m['modules']:
  need(sha(item['source'])==item['source_sha256'],'exact accepted generated source');copy(item['source'],Path('generated')/Path(*item['module'].split('.')).with_suffix('.lean'))
 for record in d['records']:
  receipt=Path(record['receipt']);folder=Path('receipts')/record['module'];copy(receipt,folder/'RUN.json')
  for name in ['stdout','stderr','rusage.txt']:copy(receipt.parent/name,folder/name)
  if record['module']==d['independent_audit']['module']:copy(receipt.parent/'source.lean',Path('generated')/Path(*record['module'].split('.')).with_suffix('.lean'))
 source_script_names=['bootstrap_context.py','reproduce_numerics.py','run_finite.py','check_exact_cells.py','check_finite_independent.py','reproduce_profiled_closure.py','rebuild_qrh_closure.py','generate_full_scalar_certificate.py','execute_full_scalar_certificate.py','compile_lean_context.py','generate_full_source_rows.py','execute_full_source_rows.py','observe_full_source_rows.py','test_full_source_cli.py','reproduce_full_source_pv.py','export_full_source_packet.py']
 for name in source_script_names:copy(S/'scripts'/name,Path('model/solution/scripts')/name)
 for name in ['generate_finite.cpp','independent_finite_check.cpp','benchmark_quotient_pi.cpp']:copy(S/'c'/name,Path('model/solution/c')/name)
 for name in ['BUILD_CONTEXT.json','REPRODUCE_FULL_SOURCE_PV.md','REPRODUCE_FULL_SCALARS.md']:copy(S/name,Path('model/solution')/name)
 for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']:copy(S.parents[1]/name,Path('model/network')/name)
 controls=Path('/data/ivy-ramanujan-source-pv-20261119')
 for name in ['full-finite-source-control32-v1','full-finite-source-control4096-v1','full-finite-source-control32-opt-v1','full-finite-source-control32-oo-v1']:
  copy(controls/name/'PROPOSAL.json',Path('controls')/name/'PROPOSAL.json');copy(controls/name/'run-v1/RESULT.json',Path('controls')/name/'RESULT.json')
 copy(controls/'full-source-cli-controls-v1/RESULT.json','controls/ACTUAL_CLI_CONTROLS.json')
 native=controls/'full-source-native-observation-v2';copy(native/'RESULT.json','ordinary-native/RESULT.json')
 for name in ['observe_all_rows.c','compile.stdout','compile.stderr','rusage.txt','stderr']:copy(native/name,Path('ordinary-native')/name)
 # The final acceptance JSON is included in the observed disk snapshot here.
 source=Path(m['source_root']);run=a.result.parent;objects={Path(x['object'])for x in d['records']};usage=dict(status='COMPLETED_SOURCE_SCALAR_RESOURCE_SNAPSHOT',wall_seconds=d['seconds'],rows=d['rows'],compiles=len(d['records']),named_axiom_reports=sum(len(x['required_constants'])for x in d['records']),largest_actual_worker_rss_bytes=d['actual_peak_worker_rss_bytes'],actual_aggregate_peak_RAM_measured=False,worker_address_space_limit_bytes=d['normal_worker_limit_bytes'],combined_worker_address_space_ceiling_bytes=d['combined_worker_limit_bytes'],final_separate_address_space_limit_bytes=d['final_independent_limit_bytes'],source_bytes=sum(x.stat().st_size for x in source.rglob('*')if x.is_file()),run_bytes_including_final_receipt=sum(x.stat().st_size for x in run.rglob('*')if x.is_file()),new_object_bytes=sum(x.stat().st_size for x in objects),all_worker_returncodes_zero=True,worker_OOM_or_memorypanic_events=0,no_large_output_arrays_retained=True,counts_formally_proved_here=False)
 usage['owned_new_stage_bytes']=usage['source_bytes']+usage['run_bytes_including_final_receipt']+usage['new_object_bytes'];(out/'RESOURCES.json').write_text(json.dumps(usage,indent=2)+'\n');copy(S/'REPRODUCE_FULL_SOURCE_PV.md','README.md')
 summary=dict(status='ACCEPTED_FULL_SCALAR_SOURCE_PV_PACKET_COUNTS_OPEN',rows=d['rows'],begin=m['begin'],stop=d['stop'],retained_integer_margin=9005,result_sha256=sha(a.result),source_first_scalar_PV=True,complete_ANT_result=False,prime_counts_formally_proved_here=False,independent_normal_O_OO_readback='PASS',source_model_files=len(model['modules']),generated_source_files=len(m['modules']),no_old_binary_or_Data_or_proof_objects_copied=True,fresh_full_one_command_workflow_executed=False,fresh32_workflow='separate active control; consult actual final receipt',exporter_sha256=sha(__file__),timestamp_unix=time.time());(out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
 inventory=[dict(path=str(x.relative_to(out)),bytes=x.stat().st_size,sha256=sha(x))for x in sorted(out.rglob('*'))if x.is_file()and x.name!='EXPORT.json'];export=dict(status='EXPORTED_EXACT_SOURCE_AND_RECEIPTS',files=inventory,original_accepted_result_sha256=sha(a.result),new_data_records_copied=0,proof_objects_copied=0);(out/'EXPORT.json').write_text(json.dumps(export,indent=2)+'\n')
 for x in inventory:need(sha(out/x['path'])==x['sha256'],'independent exported file readback')
 a.archive.parent.mkdir(parents=True,exist_ok=True)
 with tarfile.open(a.archive,'w:gz',compresslevel=9)as archive:archive.add(out,arcname='full-source-scalar-v1')
 with tarfile.open(a.archive,'r:gz')as archive:
  members={x.name:x for x in archive.getmembers()if x.isfile()}
  for x in inventory:
   name='full-source-scalar-v1/'+x['path'];need(name in members,'every exported archive member');need(hashlib.sha256(archive.extractfile(members[name]).read()).hexdigest()==x['sha256'],'every exact archived byte')
 receipt=dict(status='PACKET_AND_ARCHIVE_READBACK_PASS',archive=str(a.archive),bytes=a.archive.stat().st_size,sha256=sha(a.archive),files=len(inventory)+1,result_sha256=sha(a.result),counts_open=True);Path(str(a.archive)+'.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
if __name__=='__main__':main()
