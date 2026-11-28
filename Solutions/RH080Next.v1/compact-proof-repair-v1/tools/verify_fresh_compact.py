#!/usr/bin/env python3
"""Portable additive gate for a genuinely NEW1035/122-module compact cold replay.
Runs the unchanged fresh checker gate and adds locked original-source preservation.
No source-first C-PV claim, no promotion of a source-only proposal.
"""
import argparse,sys,time
from pathlib import Path
from compact_contract import PACKAGE,LOCKED_SHA,AUDIT,load,sha,need,publish,check_project,validate_derived

def bind(project):
    identities=check_project(project);sys.path.insert(0,str(project/'dual'))
    import verify_fft_dag_fresh_v3 as original
    need(Path(original.__file__).resolve()==(project/'dual/verify_fft_dag_fresh_v3.py').resolve(),'Fresh checker gate resolved to another project')
    need(sha(Path(original.__file__))==identities['fresh_gate']['sha256'],'Unchanged fresh gate identity differs')
    return original

def verify_math(run,context,candidate,project):
    derived=validate_derived(candidate,project);original=bind(project)
    p,r,state=original.verify_math(run,context,candidate);stage=derived['proposal']['stages'];expected=122 if stage==13 else 1035
    need(len(state['rows'])==r['modules']==expected,'Complete derived mathematical inventory missing')
    need(p['proposal']==derived['proposal'],'Fresh checker consumed another source proposal')
    audit=state['audit'];need(sha(run/'sources'/(audit+'.lean'))==AUDIT[stage],'Checker did not generate exact original typed consumer')
    need(r['audited_roots']==stage+5,'Original18/29 typed Std3 consumers missing')
    need(not any('ImportsProbe'in name for name in state['rows']),'Diagnostic probe became a mathematical provider')
    generated={row['file'][:-5]for row in derived['proposal']['modules']};foundation={row['module']for row in load(PACKAGE/'locked'/f'original-foundations-{stage}.json')['source_rows']}
    need(set(state['rows'])==generated|foundation|{f'W4D{stage}ClaimAudit'},'Extra/alternative application proof provider')
    return p,r,state

def resources(args,p,r):
    return bind(args.project_root).verify_resources(args,p,r)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['run','context','candidate','output']:ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--project-root',type=Path,default=PACKAGE.parent)
    for name in ['supervisor','command-plan','stdout','stderr']:ap.add_argument('--'+name,type=Path)
    ap.add_argument('--unit');ap.add_argument('--proof-only-toy',action='store_true');a=ap.parse_args()
    for name in ['run','context','candidate','project_root']:setattr(a,name,getattr(a,name).resolve(strict=True))
    need(not a.output.exists(),'Fresh independent receipt required');started=time.monotonic()
    p,r,state=verify_math(a.run,a.context,a.candidate,a.project_root)
    if a.proof_only_toy:need(r['stages']==13,'Toy cannot bypass N24 production resources');actual=None
    else:actual=resources(a,p,r)
    resource_inputs=None if a.proof_only_toy else dict(supervisor=str(a.supervisor),command_plan=str(a.command_plan),stdout=str(a.stdout),stderr=str(a.stderr),unit=a.unit)
    publish(a.output,dict(status='PASS_INDEPENDENT_FRESH_COMPACT_W4_KERNEL_ONLY_NOT_C_PV',stages=r['stages'],N=r['N'],modules=r['modules'],norm_numerator=r['norm_numerator'],typed_original_roots=r['audited_roots'],source_cold=True,source_cold_lineage=False,original_numeric_inventory_sha256=LOCKED_SHA[r['stages']],candidate_plan_sha256=sha(a.candidate/'PLAN.json'),transform_receipt_sha256=sha(a.candidate/'PROOF_TRANSFORM_RECEIPT.json'),result_sha256=sha(a.run/'RESULT.json'),plan_sha256=sha(a.run/'PLAN.json'),validator_sha256=sha(Path(__file__)),contract_sha256=sha(Path(__file__).with_name('compact_contract.py')),original_fresh_gate_sha256=sha(Path(bind(a.project_root).__file__)),original_checker_unchanged=True,original_numeric_source_and_data_hashes_unchanged=True,same_public31_or20_headers_and_original29_or18_typed_consumers=True,import_probe_excluded=True,full_C_source_first_PV_claimed=False,toy_only=a.proof_only_toy,actual_resource_evidence=actual,actual_resource_inputs=resource_inputs,seconds=time.monotonic()-started))
    print('PASS INDEPENDENT FRESH COMPACT KERNEL ONLY',r['stages'],flush=True)
if __name__=='__main__':main()
