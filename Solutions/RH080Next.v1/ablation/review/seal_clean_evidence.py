#!/usr/bin/env python3
"""Package completed portable proof evidence without duplicating source/proof caches."""
import argparse,json,shutil,subprocess
from pathlib import Path
import run_review as common
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--run',type=Path,required=True);ap.add_argument('--accepted',type=Path,required=True)
    ap.add_argument('--controls',type=Path,required=True);ap.add_argument('--equivalence',type=Path,required=True)
    ap.add_argument('--cgroup',type=Path,required=True);ap.add_argument('--observer',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    common.need(not args.out.exists(),'Fresh clean-evidence archive required')
    result=common.load(args.run/'RESULT.json');accepted=common.load(args.accepted);controls=common.load(args.controls/'RESULT.json');eq=common.load(args.equivalence)
    common.need(result['status']=='PASS_PORTABLE_COMMON169_PLUS_ALL13_LOCKED15_LEAN_SOURCE_COLD_STD3','Incomplete clean proof replay')
    common.need(accepted['status']=='PASS_INDEPENDENT_COMPLETED_PORTABLE169_COMMON15_LOCKED_PROOF_REPLAY' and accepted['result_sha256']==common.sha(args.run/'RESULT.json'),'Independent gate not associated')
    common.need(controls['status']=='PASS_PORTABLE_SOURCE_COLD_ACTUAL_COMPLETION_CLIS_NORMAL_O_OO' and controls['positive']==3 and controls['rejections']==15,'Actual completion controls incomplete')
    common.need(controls['validator_sha256']==accepted['validator_sha256']==common.sha(HERE/'check_clean_proofs.py'),'Executed accepted validator changed')
    common.need(eq['status']=='PASS_ALL13_LOCKED15_FULL_EXPORTS_IDENTICAL_TYPES_AXIOMS_DEPENDENCIES' and eq['clean_result_sha256']==common.sha(args.run/'RESULT.json'),'Exact mathematical export equivalence missing')
    args.out.mkdir(parents=True)
    def copy(source,relative):
        target=args.out/relative;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
        common.need(common.sha(source)==common.sha(target),'Archive byte copy differs')
    for name in ['PLAN.json','RESULT.json','SAMPLED_RESOURCES.json','reproduce_clean_proofs.executed.py']:copy(args.run/name,name)
    for path in sorted(args.run.glob('*.COMPILED.json')):copy(path,Path('compiler_receipts')/path.name)
    for path in sorted((args.run/'logs').iterdir()):
        if path.is_file():copy(path,Path('logs')/path.name)
    for source,name in [(args.accepted,'INDEPENDENT_ACCEPTED.json'),(args.controls/'RESULT.json','ACTUAL_COMPLETION_CONTROLS.json'),(args.equivalence,'FULL_EXPORT_EQUIVALENCE.json'),(args.cgroup,'OWNED_CGROUP_COMPLETION_OBSERVATION.json'),(args.observer,'observe-cgroup.executed.py')]:copy(source,name)
    cgroup=common.load(args.cgroup);samples=common.load(args.run/'SAMPLED_RESOURCES.json')['samples']
    summary=dict(status='COMPLETED_PORTABLE_PROOF_REPRODUCTION_RESOURCE_SUMMARY',seconds=result['seconds'],
       max_compiler_child_RSS_bytes=result['max_child_RSS_bytes'],sampled_aggregate_RSS_bytes=result['sampled_group_max_RSS_bytes'],sampled_aggregate_not_exact_peak=True,
       run_disk_bytes=int(subprocess.check_output(['du','-sB1',str(args.run)],text=True).split()[0]),
       max_sampled_campaign_scratch_bytes=max(x['campaign_scratch_bytes']for x in samples),
       min_sampled_host_available_bytes=result['min_sampled_MemAvailable_bytes'],failed_compilers=result['failed_compilers'],SIGKILL_compilers=result['SIGKILL_compilers'],
       actual_completed_cgroup_absolute_OOM_counters=cgroup.get('actual_completed_absolute_OOM_counters'),
       initial_unit_creation_counters_captured=False,OOM_delta_not_invented=True,
       common_sources=169,locked_sources=15,audit_modules=15,source_cold=True,original_application_objects_used=False,
       original_primary_statuses_unchanged=True,new_primary_successes=0,
       accepted_full_proof_objects_retained_in_run=str(args.run/'common/objects'),
       source_code_reproduced_from_pinned_repository=True)
    common.save(args.out/'SUMMARY.json',summary)
    adapter=common.load(HERE/'supplemental_evidence_v1/REPORT_EXPOSURE_ROWS.json')
    for row in adapter['rows']:
        if row['id'] in {r['trial']for r in result['rows']}:
            row['verification_status']='Supplemental original-D runtime and portable169+15 source-cold proof replays; Std3 export + independent mathematical reading'
    adapter['portable_clean_result_sha256']=common.sha(args.run/'RESULT.json');adapter['portable_independent_gate_sha256']=common.sha(args.accepted)
    common.save(args.out/'REPORT_EXPOSURE_ROWS_V2.json',adapter)
    members=[dict(path=str(p.relative_to(args.out)),sha256=common.sha(p),bytes=p.stat().st_size)for p in sorted(args.out.rglob('*'))if p.is_file()]
    common.save(args.out/'MANIFEST.json',dict(status='SEALED_COMPLETED_PORTABLE_CLEAN_EXPOSURE_PROOF_EVIDENCE_NOT_PRIMARY_RECLASSIFICATION',members=members,
        source_inventory_sha256=common.sha(HERE/'COMMON169_SOURCE_INPUTS.json'),seal_controller_sha256=common.sha(Path(__file__)),
        proof_objects_not_duplicated_or_deleted=True,new_primary_successes=0))
    print('SEALED accepted portable169+15+15 proof receipts, logs and exact mathematical equivalence')


if __name__=='__main__':main()
