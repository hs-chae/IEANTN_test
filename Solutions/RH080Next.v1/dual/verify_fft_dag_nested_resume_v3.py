#!/usr/bin/env python3
"""Read-only final gate for unchanged FFT mathematics across explicit phases."""
import argparse,math,os
from pathlib import Path
from reproduce_dual import need,sha,load,publish,context
import resume_fft_dag_source_cold as original
import fft_dag_nested_lineage_v3 as nested
from verify_fft_dag_lineage_resume import memory_events
HERE=Path(__file__).resolve().parent
CONTROLLER_SHA='39f3cecab3caadd32c9056c8db5e9602a4872bbe5316a5e53fa82cfd4a1baf40'
HELPER_SHA='5bbe39bcc4cb4160b9cea7421fea1cb07d46ede57e82d56dbbd7c0fab1a12465'


def verify_math(run,ctx,candidate):
    need((run/'RESULT.json').is_file(),'Missing completed nested lineage RESULT')
    p=load(run/'PLAN.json');r=load(run/'RESULT.json')
    need(p['status']=='FROZEN_V3_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV'and p['nested_schema']==3,'Wrong nested lineage plan')
    need(r['status']=='PASS_W4_INTEGER_FFT_V3_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV'and r['nested_schema']==3,'Nested mathematical proof incomplete')
    need(sha(HERE/'resume_fft_dag_source_cold_v3.py')==CONTROLLER_SHA==sha(run/'resume_driver.executed.py')==p['controller_sha256'],'Exact nested controller changed')
    need(sha(HERE/'fft_dag_nested_lineage_v3.py')==HELPER_SHA==p['continuation_helper_sha256'],'Exact nested validation helper changed')
    need(p['context_sha256']==sha(ctx),'Original exact context changed')
    c=context(ctx,original.R);prefix=Path(p['original_prefix']);parents=[Path(row['path'])for row in p['continuation_plans']]
    state=nested.validate_nested_lineage(prefix,candidate,ctx,c,parents[:-1],parents[-1])
    need(p['continuation_plans']==r['continuation_plans']==state['continuation_plans'],'Prior continuation lineage changed')
    need(p['phase_counts']==r['phase_counts']==state['phase_counts'],'Actual per-phase successful counts differ')
    need(p['original_plan_sha256']==r['original_plan_sha256']==sha(prefix/'PLAN.json')==sha(run/'ORIGINAL_SOURCE_COLD_PLAN.json'),'Original cold provenance differs')
    need(p['candidate_plan_sha256']==r['candidate_plan_sha256']==sha(candidate/'PLAN.json'),'Original candidate changed')
    need(p['sources']==state['plan']['sources']and p['payloads']==state['proposal']['payloads']and p['proposal']==state['proposal'],'Exact source/data/mathematical universe changed')
    need(p['source_cold']is False and r['source_cold']is False and p['source_cold_lineage_resume']is True and r['source_cold_lineage_resume']is True,'Nested phases falsely labeled monolithic fresh')
    need(p['outside_application_object_cache_used']is False and r['outside_application_object_cache_used']is False,'Outside application cache used')
    rows=state['rows'];reused=state['successful'];fresh=set(rows)-set(reused)
    need(p['original_successful_modules']==r['reused_original_source_cold_modules']==state['original_successful_count'],'Original phase count differs')
    need(p['inherited_continuation_modules']==r['reused_prior_continuation_modules']==state['continuation_successful_count'],'Prior continuation count differs')
    need(p['successful_prefix_modules']==r['reused_successful_source_cold_modules']==len(reused)and p['fresh_modules_required']==r['freshly_compiled_modules']==len(fresh),'Combined/fresh compiler counts differ')
    need(r['modules']==len(rows)and set(r['routes'])==set(rows)and set(p['routes'])==set(reused),'Missing/extra actual compiler route')
    peaks=[]
    for name,row in rows.items():
        logical=state['logical_origins'][name]if name in reused else run
        record=original.receipt(run,logical,row,c['compiler'],True);peaks.append(record['peak_RSS_KiB'])
        if name in reused:
            origin=state['origins'][name];route=r['routes'][name]
            expected=dict(kind='REUSED_VERIFIED_SOURCE_COLD_LINEAGE_PREFIX',compile_origin=str(origin),logical_compile_origin=str(logical),phase=state['phases'][name],receipt_sha256=sha(origin/(name+'.COMPILED.json')),object_sha256=record['object_sha256'])
            need(route==p['routes'][name]==expected and record==state['successful'][name],'Per-module original compile origin changed')
            a=origin/'objects'/(name.replace('.','/')+'.olean');b=run/'objects'/(name.replace('.','/')+'.olean')
            need(os.stat(a).st_ino==os.stat(b).st_ino and os.stat(a).st_dev==os.stat(b).st_dev,'Nested reused object was not retained as hardlink')
        else:
            need(r['routes'][name]['kind']=='FRESH_COMPILE_AFTER_VALIDATED_PREFIX','New compile mislabeled')
            expected=['/usr/bin/time','-v','-o',str(run/(name+'.time')),'prlimit','--as='+str(p['per_compiler_AS_bytes']),'--stack='+str(256*2**20),'--',*original.lean_command(c['compiler'],run,row)]
            need(record['resource_command']==expected,'New exact compiler/resource invocation differs')
    for item in p['payloads']:
        a=candidate/item['file'];b=run/'sources'/item['file']
        need(b.stat().st_size==item['bytes']and sha(b)==item['sha256'],'Fixed literal data changed')
        need(os.stat(a).st_ino==os.stat(b).st_ino and os.stat(a).st_dev==os.stat(b).st_dev,'Literal data were copied or replaced')
    expected=original.check_axioms(run,state);audit=load(run/'AXIOM_AUDIT.json')
    need(audit['status']=='PASS_UNCHANGED_ORIGINAL_TYPED_CLAIM_AND_AXIOM_AUDIT'and audit['roots']==expected and r['audited_roots']==len(expected),'Unchanged full typed/axiom audit differs')
    need(r['max_individual_RSS_KiB']==max(peaks)and original.finite_positive(r['seconds']),'Compiler resource summary invalid')
    need(r['plan_sha256']==sha(run/'PLAN.json')and r['N']==state['proposal']['n']and r['stages']==state['proposal']['stages']and r['norm_numerator']==state['proposal']['norm_numerator'],'Final fixed mathematics/result association differs')
    need(r['numerical_parameters_and_checker_mathematics_unchanged']is True and r['original_run_and_outcome_preserved']is True and r['full_original_C_FFT_PV']is False,'Incorrect source/verification tier')
    return p,r,state


def verify_resources(a,p,r):
    need(r['stages']==24 and r['N']==16777216 and r['norm_numerator']==7813568381279800,'Wrong original production result')
    need(r['phase_counts']==dict(ORIGINAL_SOURCE_COLD=992,VALIDATED_CONTINUATION_1=4,VALIDATED_NESTED_CONTINUATION_2=35),'Actual inherited phase breakdown differs')
    need(r['modules']==1033 and r['reused_original_source_cold_modules']==992 and r['reused_prior_continuation_modules']==39 and r['freshly_compiled_modules']==2,'Wrong actual992+4+35+2 phase counts')
    need(all(v is not None and v.is_file()for v in[a.supervisor,a.command_plan,a.stdout,a.stderr]),'Actual completed owned supervisor evidence required')
    s=load(a.supervisor);command=load(a.command_plan)
    need(s['status']=='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'and type(s['returncode'])is int and s['returncode']==0 and s['failure']is None,'Nested supervised child did not complete')
    need(original.finite_positive(s['seconds']),'Invalid actual supervisor wall time')
    need(s['command_file_sha256']==sha(a.command_plan)and s['command']==command['command'],'Actual command file/argument vector differs')
    expected_tail=['-u',str(HERE/'resume_fft_dag_source_cold_v3.py'),'--context',str(a.context),'--candidate',str(a.candidate.resolve()),'--prefix',p['original_prefix'],'--continuation',p['continuation_plans'][0]['path'],'--nested-continuation',p['continuation_plans'][-1]['path'],'--run',str(a.run.resolve()),'--workers','12','--worker-memory-gib','300']
    need(command['command'][1:]==expected_tail and p['workers']==12 and p['per_compiler_AS_bytes']==300*2**30,'Actual fixed invocation or virtual address cap differs')
    need(command['phases']==dict(original_source_cold=992,prior_continuation=4,prior_nested_continuation=35,new_compilation=2)and command['original_outcomes_unchanged']is True,'Declared execution phases differ')
    pins={row['path']:row['sha256']for row in command['source_pins']};need(len(pins)==len(command['source_pins']),'Duplicate execution source pin')
    for path,digest in pins.items():need(sha(Path(path))==digest,'Executed source changed '+path)
    need(pins.get(str(HERE/'resume_fft_dag_source_cold_v3.py'))==CONTROLLER_SHA and pins.get(str(HERE/'fft_dag_nested_lineage_v3.py'))==HELPER_SHA,'Reviewed controller/helper not source-pinned')
    supervisor=HERE.parent/'pv/supervise_resource_run.py';need(s['supervisor_sha256']==pins.get(str(supervisor))==sha(supervisor),'Reviewed supervisor lineage differs')
    need(s['stdout_sha256']==sha(a.stdout)and s['stderr_sha256']==sha(a.stderr),'Actual supervised logs differ')
    need(not a.stderr.read_bytes()and a.stdout.read_text().endswith('PASS_V3_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV\n'),'Missing nested completion marker or stderr diagnostic')
    before=s['before'];after=s['final'];need(a.unit and a.unit.endswith('.service'),'Concrete owned unit required')
    need(before['path']==after['path']and before['path'].startswith('/sys/fs/cgroup/')and before['path'].endswith('/'+a.unit),'Unowned or changed actual cgroup')
    for observation in[before,after]:need(observation['memory.max']==str(300*2**30)and observation['memory.swap.max']=='0','Actual300GiB/noSwap bounds differ')
    first=memory_events(before['memory.events']);last=memory_events(after['memory.events']);need(set(first)==set(last),'Owned event population differs')
    delta={k:last[k]-first[k]for k in first};need(all(v>=0 for v in delta.values())and delta['oom']==delta['oom_kill']==0,'Actual OOM events occurred or counters decreased')
    if'oom_group_kill'in delta:need(delta['oom_group_kill']==0,'Actual group OOM kill occurred')
    admission=s['admission'];need(admission['available_RAM_bytes']>=2**40 and admission['free_disk_bytes']>=2**40 and admission['owned_scratch_bytes']<270*2**30,'Actual separate admission failed')
    need(s['samples'],'Missing actual resource telemetry')
    for sample in s['samples']:need(sample['available_RAM_bytes']>=256*2**30 and sample['owned_scratch_bytes']<290*2**30 and sample['cgroup']['path']==before['path'],'Actual resource reserve/sample failed')
    return dict(actual_owned_memory_events_delta=delta,OOM_status_not_inferred_from_success=True,wall_seconds=s['seconds'],sampled_group_memory_current_max_bytes=max(int(x['cgroup']['memory.current'])for x in s['samples']),sampled_peak_not_exact=True,supervisor_sha256=sha(a.supervisor),command_plan_sha256=sha(a.command_plan),prior_interruption_final_OOM_counters='UNAVAILABLE_NOT_INFERRED')


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['run','context','candidate','output']:ap.add_argument('--'+name,type=Path,required=True)
    for name in['supervisor','command-plan','stdout','stderr']:ap.add_argument('--'+name,type=Path)
    ap.add_argument('--unit');ap.add_argument('--proof-only-toy',action='store_true');a=ap.parse_args();run=a.run.resolve()
    p,r,state=verify_math(run,a.context,a.candidate.resolve())
    if a.proof_only_toy:need(r['stages']==13,'Toy exception cannot admit N24');resources=None
    else:resources=verify_resources(a,p,r)
    publish(a.output,dict(status='PASS_INDEPENDENT_V3_NESTED_W4_FFT_SOURCE_COLD_LINEAGE_KERNEL_ONLY',stages=r['stages'],N=r['N'],norm_numerator=r['norm_numerator'],modules=r['modules'],
        reused_original_source_cold_modules=r['reused_original_source_cold_modules'],reused_prior_continuation_modules=r['reused_prior_continuation_modules'],freshly_compiled_modules=r['freshly_compiled_modules'],
        result_sha256=sha(run/'RESULT.json'),plan_sha256=sha(run/'PLAN.json'),validator_sha256=sha(Path(__file__)),source_cold=False,source_cold_lineage=True,full_C_source_first_PV_claimed=False,toy_only=a.proof_only_toy,actual_resource_evidence=resources))
    print('PASS independent nested FFT lineage: original/prior/fresh phases exact; C/ANT consumption separate')


if __name__=='__main__':main()
