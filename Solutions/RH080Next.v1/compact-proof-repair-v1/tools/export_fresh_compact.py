#!/usr/bin/env python3
"""Portable immutable source-associated bank from a genuinely fresh compact replay.
No new compilation/data execution and no source-first C-PV completion claim.
"""
import argparse,os,time
from pathlib import Path
from types import SimpleNamespace
from compact_contract import PACKAGE,load,sha,need,publish
import verify_fresh_compact as fresh

def link(source,target,digest):
    need(sha(source)==digest,'Accepted artifact changed before export');target.parent.mkdir(parents=True,exist_ok=True);os.link(source,target)
    need(source.stat().st_dev==target.stat().st_dev and source.stat().st_ino==target.stat().st_ino,'Immutable export must hardlink')

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['base','context','candidate','accepted','run']:ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--project-root',type=Path,default=PACKAGE.parent);ap.add_argument('--toy',action='store_true');a=ap.parse_args()
    for name in['base','context','candidate','accepted','project_root']:setattr(a,name,getattr(a,name).resolve(strict=True))
    need(not os.path.lexists(a.run),'Fresh immutable format bank required');started=time.monotonic();accepted=load(a.accepted)
    need(accepted['status']=='PASS_INDEPENDENT_FRESH_COMPACT_W4_KERNEL_ONLY_NOT_C_PV'and accepted['validator_sha256']==sha(Path(fresh.__file__))and accepted['contract_sha256']==sha(Path(__file__).with_name('compact_contract.py')),'Exact independent fresh compact gate required')
    need(accepted['result_sha256']==sha(a.base/'RESULT.json')and accepted['plan_sha256']==sha(a.base/'PLAN.json')and accepted['candidate_plan_sha256']==sha(a.candidate/'PLAN.json'),'Independent acceptance belongs to another run')
    need(accepted['toy_only']is a.toy,'Toy/production export scope mismatch')
    p,r,state=fresh.verify_math(a.base,a.context,a.candidate,a.project_root)
    if a.toy:need(r['stages']==13 and accepted['actual_resource_evidence']is None,'Toy cannot impersonate production resources')
    else:
        paths=accepted['actual_resource_inputs'];need(type(paths)is dict,'Actual production resource input paths required')
        args=SimpleNamespace(project_root=a.project_root,run=a.base,context=a.context,candidate=a.candidate,supervisor=Path(paths['supervisor']),command_plan=Path(paths['command_plan']),stdout=Path(paths['stdout']),stderr=Path(paths['stderr']),unit=paths['unit'])
        need(fresh.resources(args,p,r)==accepted['actual_resource_evidence'],'Actual fresh production resource acceptance changed')
    need(accepted['modules']==len(state['rows'])==(122 if a.toy else 1035),'Wrong complete mathematical inventory')
    a.run.mkdir(parents=True)
    for d in['source','objects','logs']:(a.run/d).mkdir()
    rows=[];lineage=[];generated={row['file'][:-5]for row in state['proposal']['modules']}
    for name,row in state['rows'].items():
        source=a.base/'sources'/row['file'];origin=Path(row['origin']);need(sha(source)==sha(origin)==row['sha256'],'Actual written source association changed')
        snapshot=a.run/'source'/row['file'];link(source,snapshot,row['sha256'])
        receipt_path=a.base/(name+'.COMPILED.json');raw=load(receipt_path);need(type(raw['returncode'])is int and raw['returncode']==0,'Unsuccessful compiler receipt')
        obj=a.base/'objects'/(name.replace('.','/')+'.olean');link(obj,a.run/'objects'/(name.replace('.','/')+'.olean'),raw['object_sha256'])
        for ext in['stdout','stderr','time']:link(a.base/(name+'.'+ext),a.run/'logs'/(name+'.'+ext),raw[ext+'_sha256'])
        normalized=dict(raw,exitcode=raw['returncode'],receipt_kind='FORMAT_ONLY_ACCEPTED_FRESH_COMPACT_NO_NEW_PROOF',original_compiler_receipt=str(receipt_path),original_compiler_receipt_sha256=sha(receipt_path),original_log_directory=str(a.base),original_logical_compile_directory=str(state['logical']),compile_phase='FRESH_SOURCE_COLD_COMPACT_SAME_ORIGINAL_CLAIMS',format_export_base=str(a.base),independent_acceptance=str(a.accepted),independent_acceptance_sha256=sha(a.accepted))
        publish(a.run/(name+'.COMPILED.json'),normalized)
        rows.append(dict(module=name,origin=str(origin),snapshot=str(snapshot),source_sha256=row['sha256'],imports=row['imports'],generated_source=name in generated,regeneration='Original pinned producer and original numeric inventory; deterministic compact source-only proof transform; unchanged original fresh checker.'))
        lineage.append(dict(module=name,original_receipt=str(receipt_path),original_receipt_sha256=sha(receipt_path),object_sha256=raw['object_sha256']))
    for row in state['proposal']['payloads']:link(a.base/'sources'/row['file'],a.run/'source'/row['file'],row['sha256'])
    publish(a.run/'PLAN.json',dict(status='FORMAT_ONLY_ACCEPTED_FRESH_COMPACT_BANK_NO_NEW_EXECUTION',source_rows=rows,context_sha256=sha(a.context),original_base=str(a.base),original_plan_sha256=sha(a.base/'PLAN.json'),original_result_sha256=sha(a.base/'RESULT.json'),candidate_plan_sha256=sha(a.candidate/'PLAN.json'),independent_acceptance=str(a.accepted),independent_acceptance_sha256=sha(a.accepted),per_module_lineage=lineage,source_cold=False,original_fresh_source_cold_provenance_preserved=True,application_object_fallback=False,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,controller_sha256=sha(Path(__file__))))
    publish(a.run/'RESULT.json',dict(status='PASS_FORMAT_ONLY_ACCEPTED_FRESH_COMPACT_BANK_NO_NEW_COMPILATION',sources=len(rows),objects=len(rows),independent_acceptance_sha256=sha(a.accepted),source_cold=False,original_fresh_source_cold_provenance_preserved=True,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,all_large_artifacts_hardlinked=True,original_artifacts_and_outcomes_unchanged=True,seconds=time.monotonic()-started))
    print('PASS FORMAT ONLY FRESH COMPACT BANK',len(rows),flush=True)
if __name__=='__main__':main()
