"""Rebuild the actual24 replay/resource ledger from exact preserved receipts.
Read-only scientific evidence verification; never runs a compiler, numerical job,
model, systemd scope, or deletion. Historical execution paths remain identities.
"""
from pathlib import Path
import argparse,csv,hashlib,io,json,math,re,sys
sys.dont_write_bytecode=True

def need(value,message):
    if not value: raise ValueError(message)
def strict(raw):
    def pairs(rows):
        result={}
        for key,value in rows:
            need(key not in result,'duplicate JSON key: '+key);result[key]=value
        return result
    def finite(value):
        answer=float(value);need(math.isfinite(answer),'JSON float overflow');return answer
    return json.loads(raw,object_pairs_hook=pairs,parse_float=finite,parse_constant=lambda value:(_ for _ in()).throw(ValueError('nonfinite JSON '+value)))
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
class Inputs:
    def __init__(self,source_map=None,public_root=None,require_mapped=False):
        self.mapping=strict(source_map.read_bytes())['files']if source_map else None
        self.root=public_root.resolve()if public_root else None
        self.require_mapped=require_mapped;self.checked={}
        need(not require_mapped or self.mapping is not None and self.root is not None,'mapped-only verification needs public root and source map')
    def path(self,reference):
        need(set(reference)>={'path','sha256'}and re.fullmatch('[0-9a-f]{64}',reference['sha256']),'exact path/SHA256 reference required')
        original=reference['path'];expected=reference['sha256'];path=Path(original)
        if self.require_mapped or not path.is_file():
            need(self.mapping is not None and self.root is not None,'missing original and no public source mapping: '+original)
            row=self.mapping.get(original);need(isinstance(row,dict)and row['sha256']==expected,'exact original/public source mapping absent: '+original)
            relative=Path(row['public_path']);need(not relative.is_absolute()and'..'not in relative.parts,'canonical public relative path')
            path=(self.root/relative).resolve();need(path.is_relative_to(self.root),'mapped path outside public evidence')
        need(path.is_file()and sha(path)==expected,'changed evidence bytes: '+original)
        self.checked[(original,expected)]={'path':original,'sha256':expected,'bytes':path.stat().st_size}
        return path
    def data(self,reference):return strict(self.path(reference).read_bytes())

def process_usage(text):
    result={}
    for label,key,cast in [('User time (seconds)','user_seconds',float),('System time (seconds)','system_seconds',float),('Maximum resident set size (kbytes)','maximum_resident_set_size_kib',int),('Exit status','exit_status',int)]:
        match=re.findall(r'^\s*'+re.escape(label)+r':\s*([^\n]+)$',text,re.M)
        need(len(match)==1,'unique GNU time field required: '+label);result[key]=cast(match[0])
    need(all(math.isfinite(x)for x in result.values()),'finite captured process usage')
    result['maximum_resident_set_size_bytes']=1024*result['maximum_resident_set_size_kib']
    result['measurement']='GNU time reported rusage maximum RSS; not an exact simultaneous aggregate cgroup memory peak'
    return result

def durable(inputs,reference):
    manifest=inputs.data(reference);rows=manifest['files'];need(isinstance(rows,list)and rows,'nonempty durable manifest')
    total=0;unique=set();time_rows=[]
    for row in rows:
        need(set(row)>={'original','durable','bytes'}and row['original']['sha256']==row['durable']['sha256'],'exact durable/original byte identity')
        key=row['durable']['path'];need(key not in unique,'duplicate durable path');unique.add(key)
        target=inputs.path(row['durable']);need(target.stat().st_size==row['bytes'],'durable size differs');total+=row['bytes']
        if Path(row['original']['path']).name=='PROCESS_RUSAGE.txt':time_rows.append((row['durable'],process_usage(target.read_text())))
    need(len(time_rows)==1,'one exact process-rusage capture per full attempt')
    return len(rows),total,{'source':time_rows[0][0],**time_rows[0][1]}

def main():
    parser=argparse.ArgumentParser(allow_abbrev=False);parser.add_argument('--selection',type=Path,required=True);parser.add_argument('--out',type=Path,required=True);parser.add_argument('--source-map',type=Path);parser.add_argument('--public-root',type=Path);parser.add_argument('--require-mapped',action='store_true');args=parser.parse_args()
    need(not args.out.exists()and args.out.parent.is_dir(),'fresh output directory with existing parent')
    inputs=Inputs(args.source_map,args.public_root,args.require_mapped);selection=strict(args.selection.read_bytes());need(selection['schema']=='EXACT_FINAL24_ACTUAL_NUMERICAL_RESULT_SELECTION_V1','exact selection schema');success=[]
    for ref in selection['successful_cases']:
        record=inputs.data(ref);cid=record['candidate_id'];need(record['status'].startswith('PASS_'),'successful actual readback')
        for field in ['exact_original_mathematical_output_contracts_reproduced','unchanged_adapter_verify_outputs_independently_called','execution_drained','reservation_released','cgroup_and_lease_absent','source_math_algorithm_parameters_and_original_outcomes_unchanged']:
            need(record[field]is True,cid+' incomplete '+field)
        need(record['actual_dead_unit_state']=={'MainPID':'0','ActiveState':'inactive'}and record['model_calls']==0 and record['source_first_PV']is False and record['full_analytic_Lean']is False,'exact historical drain and trust boundary')
        final=inputs.data(record['actual_final_receipt']);numerical=inputs.data(record['actual_numerical_receipt']);resource=inputs.data(record['actual_resource']);inputs.path(record['archive']);job=inputs.data(final['job'])
        need(final['status']=='PASS_EXACT_NUMERICAL_REPRODUCTION_AND_ACTUAL_DRAIN'and final['candidate_id']==cid and final['execution_drained']is True and final['reservation_released']is True and final['numerical_receipt']==record['actual_numerical_receipt']and final['resource_receipt']==record['actual_resource'],'exact final/numerical/resource chain')
        need(numerical['status']=='ALL_CHILDREN_AND_FULL_ARTIFACTS_REPRODUCED_AWAITING_EXTERNAL_DRAIN'and numerical['candidate_id']==cid and all(row['passed']is True for row in numerical['jobs']),'all actual full child outcomes')
        need(resource['returncode']==0 and resource['error']is None and resource['execution_drained']is True and resource['reservation_released']is True,'complete actual resource status')
        top=record.get('actual_full_top_level_routes',record.get('full_top_level_route_count'));nested=record.get('nested_active_routes',record.get('nested_routes',record.get('full_nested_route_count')))
        need(type(top)is int and type(nested)is int and top==len(numerical['jobs'])and top+nested==job['complete_active_cli_and_compile_route_count'],'exact full top/nested route census')
        files,size,usage=durable(inputs,record['durable_copy_manifest']);need(files==record['durably_preserved_files']and size==record.get('durably_preserved_payload_bytes',record.get('durable_allocated_payload_bytes'))and usage['exit_status']==0,'durable file/byte census and GNU process exit')
        sealref=selection['latest_qualified_math_portfolios'][cid];seal=inputs.data(sealref);need(seal['candidate_id']==cid and seal['reviewed_by']=='/root'and seal['status'].startswith('ROOT_FINALIZED_FULL_'),'latest qualified Root mathematical portfolio')
        peak=resource['exact_aggregate_memory_peak_bytes'];need(peak is None,'report exact aggregate peak as unavailable on the recorded kernel')
        oom=dict(line.split()for line in resource['OOM_events_last_observed'].splitlines());need(all(int(x)==0 for x in oom.values()),'successful attempt OOM counter unexpectedly nonzero')
        need(record['elapsed_seconds']==resource['elapsed_seconds']and record['sampled_charged_RAM_peak_lower_bound_bytes']==resource['sampled_charged_RAM_peak_lower_bound_bytes'],'same actual resource measurements')
        reservation=resource['reservation'];need(reservation['memory_bytes']==64*1024**3 and reservation['cpus']==8 and reservation['scratch_bytes']==25*1024**3,'equivalent64GiB8CPU25GiB policy')
        success.append({'candidate_id':cid,'stage_id':seal['stage_id'],'status':'ACTUAL_FULL_NUMERICAL_REPLAY_VERIFIED_AND_DRAINED','top_level_routes':top,'nested_routes':nested,'total_required_routes':top+nested,'actual_source_root':record['source_root'],'actual_source_archive':record['archive'],'actual_original_readback':ref,'actual_final_receipt':record['actual_final_receipt'],'actual_numerical_receipt':record['actual_numerical_receipt'],'actual_resource_receipt':record['actual_resource'],'original_job':final['job'],'qualified_math_portfolio':sealref,'elapsed_seconds':resource['elapsed_seconds'],'sampled_charged_RAM_peak_lower_bound_bytes':resource['sampled_charged_RAM_peak_lower_bound_bytes'],'exact_aggregate_memory_peak_bytes':None,'last_observed_memory_events':{k:int(v)for k,v in oom.items()},'retained_host_output_usage_after_execution':resource['retained_output_usage'],'peak_disk_bytes':None,'private_tmpfs_scratch_limit_bytes':reservation['scratch_bytes'],'reserved_RAM_bytes':reservation['memory_bytes'],'reserved_CPUs':reservation['cpus'],'captured_process_usage':usage,'durable_copy_manifest':record['durable_copy_manifest'],'durable_files':files,'durable_payload_bytes':size,'historical_unit_state':record['actual_dead_unit_state'],'cgroup_and_lease_absent_when_checked':True,'all_original_mathematics_algorithms_parameters_and_outcomes_preserved':True,'full_analytic_Lean':False,'source_first_PV':False,'new_verified_network_node':False,'source_claim_audit_status':'Full qualified Root portfolio assessment at stated written proof, named-literature and ordinary numerical execution tier; rejected or restricted historical claims are preserved separately.'})
    success.sort(key=lambda row:row['candidate_id']);need([row['candidate_id']for row in success]==['FOLLOWUP-C%03d'%i for i in range(1,25)],'exact24 unique canonical actual successful cases');need(sum(row['total_required_routes']for row in success)==595,'exact595 required routes')
    failures=[]
    for ref in selection['failed_attempts_separate']:
        record=inputs.data(ref);resource=inputs.data(record['actual_resource']);need(record['no_FINAL_REPRODUCTION_RECEIPT_exists']is True and record['execution_drained']is True and record['reservation_released']is True and record['cgroup_and_lease_absent']is True and resource['returncode']==1,'preserved failed attempt, never completion');files,size,usage=durable(inputs,record['durable_copy_manifest']);need(files==record['files_preserved']and size==record['bytes_preserved'],'failed durable history size');failures.append({'candidate_id':'FOLLOWUP-C022','attempt':'first actual final24 replay','status':'INCOMPLETE_REPLAY_COMMAND_PATH_FRAMING_FAILURE_NOT_MATHEMATICAL_OR_OOM_FAILURE','actual_readback':ref,'actual_resource':record['actual_resource'],'actual_source_root':record['actual_root'],'elapsed_seconds':resource['elapsed_seconds'],'sampled_charged_RAM_peak_lower_bound_bytes':resource['sampled_charged_RAM_peak_lower_bound_bytes'],'exact_aggregate_memory_peak_bytes':None,'last_observed_memory_events':resource['OOM_events_last_observed'],'retained_host_output_usage_after_execution':resource['retained_output_usage'],'peak_disk_bytes':None,'captured_process_usage':usage,'durable_copy_manifest':record['durable_copy_manifest'],'durable_files':files,'durable_payload_bytes':size,'first20_original_command_records_matched':len(record['all_first20_full_original_streams_independently_matched']),'final_consumer_and17_output_checks_not_reached':True,'execution_drained':True,'reservation_released':True,'cgroup_and_lease_absent_when_checked':True,'failure_cause':'The initial historical auxiliary script was replayed at its later saved filename ancillary-initial.py instead of its actual original execution path ancillary.py; stdout and expected exit1 matched, while the literal stderr filename contract rejected. The subsequent successful replay uses recovered exact original path/source history, without changing algorithms, parameters, mathematics or output contracts.'})
    need(len(failures)==1,'exactly one separately preserved failed C022 attempt in this final completion ledger')
    result={'schema':'COMPLETE_FINAL24_ACTUAL_NUMERICAL_RESOURCE_AND_REPRODUCTION_LEDGER_V1','status':'ALL24_ACTUAL_UNIQUE_FULL_CASES_COMPLETED_AND_HASH_CHECKED_WITH_FAILED_ATTEMPT_SEPARATE','selection_sha256':sha(args.selection),'builder_sha256':sha(Path(__file__)),'selection_rule':selection['selection_rule'],'completed_unique_cases':24,'total_required_routes':595,'successful_cases':success,'failed_attempts_separate':failures,'all_original_experimental_outcomes_unchanged':True,'no_scientific_jobs_or_compilers_rerun_by_ledger':True,'exact_aggregate_memory_peak_unavailable':'The recorded Linux5.15 kernel has no memory.peak file; sampled charged RAM is a lower bound, GNU time RSS is a separate rusage observation, reserved RAM is only a limit.','disk_measurement_scope':'retained_host_output_usage_after_execution is a recorded post-run apparent/allocated host-output measurement, not a peak; private work24GiB plus temporary1GiB were bounded tmpfs and are not inferred persistent host disk usage.','elapsed_measurement_scope':'Recorded per-attempt scientific resource-controller elapsed wall time; summing sequential/overlapping cases does not represent campaign wall time or model effort.','source_first_PV':False,'full_analytic_Lean':False,'new_verified_network_nodes':0,'general_exposure_advantage_established':False,'input_references_checked':sorted(inputs.checked.values(),key=lambda row:(row['path'],row['sha256']))}
    args.out.mkdir();(args.out/'FINAL24_ACTUAL_NUMERICAL_RESOURCE_LEDGER.json').write_text(json.dumps(result,indent=2,sort_keys=True,allow_nan=False)+'\n');stream=io.StringIO();fields=['candidate_id','stage_id','total_required_routes','elapsed_seconds','sampled_charged_RAM_peak_lower_bound_bytes','GNU_time_maximum_RSS_bytes','GNU_time_user_seconds','GNU_time_system_seconds','retained_host_apparent_bytes','retained_host_allocated_bytes','durable_files','durable_payload_bytes'];writer=csv.DictWriter(stream,fieldnames=fields,delimiter='\t');writer.writeheader()
    for row in success:writer.writerow({**{key:row[key]for key in fields if key in row},'GNU_time_maximum_RSS_bytes':row['captured_process_usage']['maximum_resident_set_size_bytes'],'GNU_time_user_seconds':row['captured_process_usage']['user_seconds'],'GNU_time_system_seconds':row['captured_process_usage']['system_seconds'],'retained_host_apparent_bytes':row['retained_host_output_usage_after_execution']['apparent_bytes'],'retained_host_allocated_bytes':row['retained_host_output_usage_after_execution']['allocated_bytes']})
    (args.out/'FINAL24_ACTUAL_NUMERICAL_RESOURCE_TABLE.tsv').write_text(stream.getvalue());print(json.dumps({'status':result['status'],'completed_unique_cases':24,'required_routes':595,'successful_durable_files_checked':sum(row['durable_files']for row in success),'successful_durable_payload_bytes_checked':sum(row['durable_payload_bytes']for row in success),'failed_attempts_preserved':len(failures),'exact_source_and_receipt_references_checked':len(inputs.checked),'output_ledger_sha256':sha(args.out/'FINAL24_ACTUAL_NUMERICAL_RESOURCE_LEDGER.json'),'scope_model_compiler_numerical_deletion_calls':0},sort_keys=True))
if __name__=='__main__':main()
