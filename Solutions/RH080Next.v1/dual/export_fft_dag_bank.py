#!/usr/bin/env python3
"""FORMAT ONLY: expose accepted FFT proof objects to source-associated consumers.
No compilation, numerical execution or new proof is performed. All large objects,
source and literal snapshots are hardlinked. Actual per-module origins survive.
"""
import argparse,os,sys,time
from pathlib import Path
from reproduce_dual import need,sha,load,publish,context
import resume_fft_dag_source_cold as old
import verify_fft_dag_nested_resume as nested_gate
import verify_fft_dag_lineage_resume as first_gate


def link(source,target,digest):
    need(sha(source)==digest,'Accepted artifact changed before format export')
    target.parent.mkdir(parents=True,exist_ok=True);os.link(source,target)
    need(os.stat(source).st_ino==os.stat(target).st_ino and os.stat(source).st_dev==os.stat(target).st_dev,'Format export must hardlink, never copy')


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['base','context','candidate','accepted','run']:ap.add_argument('--'+name,type=Path,required=True)
    ap.add_argument('--toy',action='store_true');a=ap.parse_args();base=a.base.resolve();candidate=a.candidate.resolve()
    need(not os.path.lexists(a.run),'Fresh format-only bank required');began=time.monotonic()
    accepted=load(a.accepted);result=load(base/'RESULT.json');plan=load(base/'PLAN.json')
    need(accepted['result_sha256']==sha(base/'RESULT.json')and accepted['plan_sha256']==sha(base/'PLAN.json'),'Independent acceptance is for another proof run')
    if result['status']=='PASS_W4_INTEGER_FFT_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV':
        need(accepted['status']=='PASS_INDEPENDENT_NESTED_W4_FFT_SOURCE_COLD_LINEAGE_KERNEL_ONLY'and accepted['validator_sha256']==sha(Path(nested_gate.__file__)),'Nested independent gate missing or changed')
        p,r,state=nested_gate.verify_math(base,a.context,candidate)
        origins={name:state['origins'].get(name,base)for name in state['rows']}
        logical={name:state['logical_origins'].get(name,base)for name in state['rows']}
        phases={name:state['phases'].get(name,'CURRENT_FRESH_COMPILATION')for name in state['rows']}
        counts=dict(original=r['reused_original_source_cold_modules'],prior_continuation=r['reused_prior_continuation_modules'],current_fresh=r['freshly_compiled_modules'])
    elif result['status']=='PASS_W4_INTEGER_FFT_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV':
        need(accepted['status']=='PASS_INDEPENDENT_FIXED_W4_FFT_SOURCE_COLD_LINEAGE_RESUME_KERNEL_ONLY'and accepted['validator_sha256']==sha(Path(first_gate.__file__)),'First-lineage independent gate missing or changed')
        p,r,state=first_gate.verify_math(base,a.context,candidate);origins={n:Path(p['original_prefix'])if n in state['successful']else base for n in state['rows']};logical={n:state['logical']if n in state['successful']else base for n in state['rows']};phases={n:'ORIGINAL_SOURCE_COLD'if n in state['successful']else'CURRENT_FRESH_COMPILATION'for n in state['rows']};counts=dict(original=len(state['successful']),prior_continuation=0,current_fresh=r['freshly_compiled_modules'])
    elif result['status']=='PASS_W4_COMPLETE_INTEGER_FFT_TRACE_CHECKED_TWIDDLES_AND_NUMERATOR_NOT_SOURCE_PV':
        # Also usable for a clean original-v2 bank once a distinct independent
        # original-cold gate has accepted that exact result/plan.
        need(accepted['status']=='PASS_INDEPENDENT_ORIGINAL_W4_FFT_SOURCE_COLD_KERNEL_ONLY','Independent original-cold gate required')
        c=context(a.context,old.R);state=old.validate_prefix(base,candidate,a.context,c);need(len(state['successful'])==len(state['rows']),'Original clean proof run incomplete');old.check_axioms(base,state)
        p=plan;r=result;origins={n:base for n in state['rows']};logical={n:state['logical']for n in state['rows']};phases={n:'ORIGINAL_FRESH_SOURCE_COLD'for n in state['rows']};counts=dict(original=len(state['rows']),prior_continuation=0,current_fresh=0)
    else:raise ValueError('Unaccepted/unsupported FFT proof result')
    if a.toy:need(r['stages']==13 and accepted['toy_only']is True,'Toy format export only stage13')
    else:need(r['stages']==24 and accepted['toy_only']is False and accepted['actual_resource_evidence']is not None,'Actual N24 independent resource acceptance required')
    need(accepted['modules']==len(state['rows'])and accepted['norm_numerator']==r['norm_numerator'],'Independent mathematical scope differs')
    a.run.mkdir(parents=True);(a.run/'objects').mkdir();(a.run/'source').mkdir();(a.run/'logs').mkdir();rows=[];lineage=[]
    for name,row in state['rows'].items():
        source=base/'sources'/row['file'];snapshot=a.run/'source'/row['file'];link(source,snapshot,row['sha256'])
        origin=Path(row['origin']);need(sha(origin)==row['sha256'],'Original written source changed')
        receipt_path=origins[name]/(name+'.COMPILED.json');raw=load(receipt_path)
        need(raw==load(base/(name+'.COMPILED.json'))and raw['returncode']==0,'Original per-module compiler provenance differs')
        obj=base/'objects'/(name.replace('.','/')+'.olean');target=a.run/'objects'/(name.replace('.','/')+'.olean');link(obj,target,raw['object_sha256'])
        for ext in['stdout','stderr','time']:link(origins[name]/(name+'.'+ext),a.run/'logs'/(name+'.'+ext),raw[ext+'_sha256'])
        normalized=dict(raw,exitcode=raw['returncode'],receipt_kind='FORMAT_ONLY_EXISTING_VERIFIED_COMPILATION_NO_NEW_PROOF',
            original_compiler_receipt=str(receipt_path),original_compiler_receipt_sha256=sha(receipt_path),original_log_directory=str(origins[name]),
            original_logical_compile_directory=str(logical[name]),compile_phase=phases[name],format_export_base=str(base),
            independent_acceptance=str(a.accepted),independent_acceptance_sha256=sha(a.accepted))
        publish(a.run/(name+'.COMPILED.json'),normalized)
        rows.append(dict(module=name,origin=str(origin),snapshot=str(snapshot),source_sha256=row['sha256'],imports=row['imports'],
            generated_source=name in{item['file'][:-5]for item in state['proposal']['modules']},
            regeneration='dual/produce_fft_dag_certificate.py with original pinned PLAN; dual/reproduce_fft_dag_v2.py or explicit same-experiment continuation'))
        lineage.append(dict(module=name,phase=phases[name],original_receipt=str(receipt_path),original_receipt_sha256=sha(receipt_path),object_sha256=raw['object_sha256']))
    for item in state['proposal']['payloads']:link(base/'sources'/item['file'],a.run/'source'/item['file'],item['sha256'])
    publish(a.run/'PLAN.json',dict(status='FORMAT_ONLY_ACCEPTED_FFT_DAG_BANK_NO_NEW_EXECUTION',source_rows=rows,context_sha256=sha(a.context),original_base=str(base),original_plan_sha256=sha(base/'PLAN.json'),original_result_sha256=sha(base/'RESULT.json'),independent_acceptance=str(a.accepted),independent_acceptance_sha256=sha(a.accepted),compile_phases=counts,per_module_lineage=lineage,
        source_cold=False,source_cold_lineage_preserved=True,application_object_fallback=False,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,controller_sha256=sha(Path(__file__))))
    publish(a.run/'RESULT.json',dict(status='PASS_FORMAT_ONLY_ACCEPTED_FFT_DAG_BANK_NO_NEW_COMPILATION',sources=len(rows),objects=len(rows),compile_phases=counts,
        independent_acceptance_sha256=sha(a.accepted),source_cold=False,source_cold_lineage_preserved=True,new_compilation=False,new_numerical_run=False,source_first_PV_complete=False,
        all_large_artifacts_hardlinked=True,original_artifacts_and_outcomes_unchanged=True,seconds=time.monotonic()-began))
    print('PASS format-only FFT source/receipt bank; no new proof, execution or PV claim')


if __name__=='__main__':main()
