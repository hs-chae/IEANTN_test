#!/usr/bin/env python3
"""Immutable format-only compact proof bank; no computation, compilation, or C-PV claim."""
import argparse,os,time
from pathlib import Path
from types import SimpleNamespace
import verify_compact_final as gate
from verify_compact_final import load,need,sha,publish

def link(source,target,digest):
    need(sha(source)==digest,'Accepted artifact changed before export')
    target.parent.mkdir(parents=True,exist_ok=True)
    os.link(source,target)
    need(os.stat(source).st_dev==os.stat(target).st_dev and os.stat(source).st_ino==os.stat(target).st_ino,'Export must hardlink immutable bytes')

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['base','assembly','context','accepted','run']:ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--toy',action='store_true');a=ap.parse_args()
    for name in['base','assembly','context','accepted']:setattr(a,name,getattr(a,name).resolve(strict=True))
    need(not os.path.lexists(a.run),'Fresh format-only export required');began=time.monotonic()
    accepted=load(a.accepted)
    need(accepted['status']=='PASS_INDEPENDENT_COMPACT_NUMERICAL_KERNEL_ONLY_NOT_C_PV'and accepted['validator_sha256']==sha(Path(gate.__file__)),'Current independent compact gate required')
    need(accepted['plan_sha256']==sha(a.base/'PLAN.json')and accepted['result_sha256']==sha(a.base/'RESULT.json')and accepted['assembly_sha256']==sha(a.assembly/'ASSEMBLY.json'),'Acceptance belongs to another proof run')
    need(accepted['toy_only']is a.toy,'Explicit export verification tier differs')
    state=gate.verify_math(a.base,a.assembly,a.context,a.toy)
    if not a.toy:
        ev=accepted['actual_resource_evidence'];need(type(ev)is dict,'Actual complete N24 resource acceptance required')
        args=SimpleNamespace(run=a.base,assembly=a.assembly,supervisor=Path(ev['supervisor']),command_plan=Path(ev['command_plan']),unit_policy=Path(ev['unit_policy']),page_policy=Path(ev['page_policy']))
        need(gate.verify_resources(args,state)==ev,'Actual resource acceptance changed')
    else:need(accepted['actual_resource_evidence']is None,'Toy export must not impersonate production resource evidence')
    stage=state['assembly']['stage'];bank=state['bank'];oldrows=state['oldrows'];base=state['base'];plan=state['plan']
    names=list(state['inherited'])+['TopShapeSymbolic','NormSymbolic',f'W4D{stage}Final',f'W4D{stage}ClaimAudit']
    need(len(names)==accepted['math_bank_modules']==(122 if a.toy else 1035),'Wrong mathematical provider count')
    a.run.mkdir(parents=True)
    for d in['source','objects','logs','diagnostics']:(a.run/d).mkdir()
    rows=[];lineage=[];counts={}
    newrows={r['module']:r for r in plan['modules']}
    for name in names:
        if name in state['inherited']:
            row=oldrows[name];source=bank/'sources'/row['file'];origin=Path(row['origin']);imports=row['imports'];source_sha=row['sha256']
            route=base.get('routes',{}).get(name)
            compile_origin=Path(route['compile_origin'])if route else bank
            logical=Path(route['logical_compile_origin'])if route else bank
            phase=route['phase']if route else'ORIGINAL_SOURCE_COLD'
            receipt_path=compile_origin/(name+'.COMPILED.json');raw=load(receipt_path)
            need(raw==load(bank/(name+'.COMPILED.json')),'Original actual compiler receipt changed')
            log_root=compile_origin
        else:
            row=newrows[name];source=a.assembly/row['file'];origin=source;imports=row['imports'];source_sha=row['sha256']
            compile_origin=a.base;logical=a.base;phase='FRESH_COMPACT_PROOF_ONLY_SAME_MATHEMATICAL_CLAIMS'
            receipt_path=a.base/(name+'.COMPILED.json');raw=state['new'][name];log_root=a.base
        need(sha(origin)==sha(source)==source_sha,'Written source association differs')
        snapshot=a.run/'source'/(name.replace('.','/')+'.lean');link(source,snapshot,source_sha)
        obj=a.base/'objects'/(name.replace('.','/')+'.olean');link(obj,a.run/'objects'/(name.replace('.','/')+'.olean'),raw['object_sha256'])
        for ext in['stdout','stderr','time']:link(log_root/(name+'.'+ext),a.run/'logs'/(name+'.'+ext),raw[ext+'_sha256'])
        if raw.get('marker_sha256')is not None:link(a.base/(name+'.markers'),a.run/'logs'/(name+'.markers'),raw['marker_sha256'])
        normalized=dict(raw,exitcode=raw['returncode'],receipt_kind='FORMAT_ONLY_EXISTING_VERIFIED_COMPILATION_NO_NEW_PROOF',original_compiler_receipt=str(receipt_path),original_compiler_receipt_sha256=sha(receipt_path),original_log_directory=str(log_root),original_logical_compile_directory=str(logical),compile_phase=phase,format_export_base=str(a.base),independent_acceptance=str(a.accepted),independent_acceptance_sha256=sha(a.accepted))
        publish(a.run/(name+'.COMPILED.json'),normalized)
        rows.append(dict(module=name,origin=str(origin),snapshot=str(snapshot),source_sha256=source_sha,imports=imports,generated_source=name not in state['inherited'],regeneration='Original pinned numerical producer/checker for inherited sources; generate_compact_final_v2.py with exact original source and helper pins for compact proof assembly.'))
        lineage.append(dict(module=name,phase=phase,original_receipt=str(receipt_path),original_receipt_sha256=sha(receipt_path),object_sha256=raw['object_sha256']))
        counts[phase]=counts.get(phase,0)+1
    for row in base['payloads']:link(bank/'sources'/row['file'],a.run/'source'/row['file'],row['sha256'])
    probe=f'W4D{stage}FinalImportsProbe'
    for ext in['COMPILED.json','stdout','stderr','time','markers']:
        source=a.base/(probe+'.'+ext)
        if source.is_file():link(source,a.run/'diagnostics'/(probe+'.'+ext),sha(source))
    link(a.assembly/(probe+'.lean'),a.run/'diagnostics'/(probe+'.lean'),newrows[probe]['sha256'])
    link(a.base/'objects'/(probe+'.olean'),a.run/'diagnostics'/(probe+'.olean'),state['new'][probe]['object_sha256'])
    publish(a.run/'PLAN.json',dict(status='FORMAT_ONLY_ACCEPTED_COMPACT_FFT_BANK_NO_NEW_EXECUTION',source_rows=rows,context_sha256=sha(a.context),original_base=str(a.base),original_plan_sha256=sha(a.base/'PLAN.json'),original_result_sha256=sha(a.base/'RESULT.json'),independent_acceptance=str(a.accepted),independent_acceptance_sha256=sha(a.accepted),compile_phases=counts,per_module_lineage=lineage,math_bank_modules=len(rows),actual_fresh_compiler_calls=5,diagnostic_import_probe_excluded_from_math_bank=True,payloads=base['payloads'],source_cold=False,inherited_numerical_source_cold_lineage_preserved=True,fresh_proof_modules_are_associated_not_source_cold=True,application_object_fallback=False,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,controller_sha256=sha(Path(__file__))))
    publish(a.run/'RESULT.json',dict(status='PASS_FORMAT_ONLY_ACCEPTED_COMPACT_FFT_BANK_NO_NEW_COMPILATION',sources=len(rows),objects=len(rows),compile_phases=counts,independent_acceptance_sha256=sha(a.accepted),source_cold=False,inherited_numerical_source_cold_lineage_preserved=True,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,all_large_artifacts_hardlinked=True,original_artifacts_and_outcomes_unchanged=True,diagnostic_import_probe_not_a_mathematical_provider=True,seconds=time.monotonic()-began))
    print('PASS FORMAT ONLY COMPACT BANK',len(rows),flush=True)
if __name__=='__main__':main()
