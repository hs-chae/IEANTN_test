#!/usr/bin/env python3
"""Independently revalidate a completed same-experiment FFT proof continuation.

N24 requires actual owned supervisor/resource observations. Toy mode is limited
strictly to stage13 and still rechecks the full mathematical lineage and claims.
"""
import argparse,math,os,re
from pathlib import Path
from reproduce_dual import need,sha,load,publish,context
import resume_fft_dag_source_cold as resume
HERE=Path(__file__).resolve().parent
CONTROLLER_SHA='04421c858331351ed4e2dbf3bd7e13c3bac10182fb2c14c852fd1567afb5afa8'


def memory_events(text):
    result={}
    for line in text.splitlines():
        pair=line.split();need(len(pair)==2 and pair[0]not in result and pair[1].isdigit(),'Invalid owned memory.events')
        result[pair[0]]=int(pair[1])
    need({'oom','oom_kill'}<=set(result),'Missing actual owned OOM counters')
    return result


def verify_math(run,context_path,candidate):
    need((run/'RESULT.json').is_file(),'Missing completed lineage RESULT')
    p=load(run/'PLAN.json');r=load(run/'RESULT.json')
    need(r['status']=='PASS_W4_INTEGER_FFT_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV','Not a completed unchanged mathematical continuation')
    need(p['status']=='FROZEN_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV','Wrong lineage PLAN')
    need(sha(HERE/'resume_fft_dag_source_cold.py')==CONTROLLER_SHA==sha(run/'resume_driver.executed.py')==p['controller_sha256'],'Exact executed resume controller differs')
    need(p['context_helper_sha256']==resume.CONTEXT_HELPER_SHA and sha(HERE/'reproduce_dual.py')==resume.CONTEXT_HELPER_SHA,'Context validator changed')
    need(p['context_sha256']==sha(context_path),'Exact original context changed')
    c=context(context_path,resume.R);prefix=Path(p['original_prefix']);state=resume.validate_prefix(prefix,candidate,context_path,c)
    need(p['original_plan_sha256']==sha(prefix/'PLAN.json')==sha(run/'ORIGINAL_SOURCE_COLD_PLAN.json')==r['original_plan_sha256'],'Original source-cold plan lineage differs')
    need(p['candidate_plan_sha256']==sha(candidate/'PLAN.json')==r['candidate_plan_sha256'],'Original candidate changed')
    need(p['sources']==state['plan']['sources'] and p['payloads']==state['proposal']['payloads'] and p['proposal']==state['proposal'],'Source/data/mathematical universe changed')
    need(p['source_cold'] is False and r['source_cold'] is False and p['source_cold_lineage_resume'] is True and r['source_cold_lineage_resume'] is True,'Resume mislabeled monolithic fresh')
    need(p['outside_application_object_cache_used'] is False and r['outside_application_object_cache_used'] is False,'Outside application cache used')
    rows=state['rows'];reused=state['successful'];fresh=set(rows)-set(reused)
    need(p['successful_prefix_modules']==r['reused_successful_source_cold_modules']==len(reused),'Successful prefix count differs')
    need(p['fresh_modules_required']==r['freshly_compiled_modules']==len(fresh) and r['modules']==len(rows),'Fresh/total module count differs')
    need(set(r['routes'])==set(rows) and set(p['routes'])==set(reused),'Omitted or extra compiler route')
    peaks=[]
    for name,row in rows.items():
        record=resume.receipt(run,state['logical']if name in reused else run,row,c['compiler'],True)
        peaks.append(record['peak_RSS_KiB'])
        if name in reused:
            need(record==reused[name] and sha(run/(name+'.COMPILED.json'))==sha(prefix/(name+'.COMPILED.json')),'Reused receipt provenance changed')
            need(r['routes'][name]==p['routes'][name] and r['routes'][name]['kind']=='REUSED_SUCCESSFUL_ORIGINAL_SOURCE_COLD_PREFIX','Reused route misclassified')
            original=prefix/'objects'/(name.replace('.','/')+'.olean');linked=run/'objects'/(name.replace('.','/')+'.olean')
            need(os.stat(original).st_ino==os.stat(linked).st_ino and os.stat(original).st_dev==os.stat(linked).st_dev,'Accepted prefix object was not retained as hardlink')
        else:
            need(r['routes'][name]['kind']=='FRESH_COMPILE_AFTER_VALIDATED_PREFIX','Fresh route misclassified')
            expected=['/usr/bin/time','-v','-o',str(run/(name+'.time')),'prlimit','--as='+str(p['per_compiler_AS_bytes']),'--stack='+str(256*2**20),'--',*resume.lean_command(c['compiler'],run,row)]
            need(record['resource_command']==expected,'Fresh exact compiler/resource command differs')
    for item in p['payloads']:
        source=candidate/item['file'];snapshot=run/'sources'/item['file']
        need(snapshot.stat().st_size==item['bytes'] and sha(snapshot)==item['sha256'],'Staged fixed literal data changed')
        need(os.stat(source).st_ino==os.stat(snapshot).st_ino and os.stat(source).st_dev==os.stat(snapshot).st_dev,'Literal snapshots were copied or replaced')
    expected_audits=resume.check_axioms(run,state);audits=load(run/'AXIOM_AUDIT.json')
    need(audits['status']=='PASS_UNCHANGED_ORIGINAL_TYPED_CLAIM_AND_AXIOM_AUDIT' and audits['roots']==expected_audits and r['audited_roots']==len(expected_audits),'Unchanged typed claim/axiom audit differs')
    need(r['plan_sha256']==sha(run/'PLAN.json'),'Completed plan hash differs')
    need(r['max_individual_RSS_KiB']==max(peaks),'Actual compiler peakRSS summary differs')
    need(resume.finite_positive(r['seconds']),'Invalid measured continuation elapsed time')
    need(r['N']==state['proposal']['n'] and r['stages']==state['proposal']['stages'] and r['norm_numerator']==state['proposal']['norm_numerator'],'Fixed original grid/numerator differs')
    need(r['numerical_parameters_and_checker_mathematics_unchanged'] is True and r['original_run_and_outcome_preserved'] is True and r['full_original_C_FFT_PV'] is False,'Incorrect mathematical/provenance scope')
    return p,r,state


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['run','context','candidate','output']:ap.add_argument('--'+name,type=Path,required=True)
    for name in ['supervisor','resource-plan','stdout','stderr','unit-properties']:ap.add_argument('--'+name,type=Path)
    ap.add_argument('--proof-only-toy',action='store_true');a=ap.parse_args();run=a.run.resolve()
    p,r,state=verify_math(run,a.context,a.candidate.resolve());resource=None
    if a.proof_only_toy:
        need(r['stages']==13,'Toy resource exception cannot admit N24')
    else:
        need(r['stages']==24 and r['N']==16777216 and r['norm_numerator']==7813568381279800,'Wrong production mathematical scope')
        need(r['modules']==1033 and r['reused_successful_source_cold_modules']==992 and r['freshly_compiled_modules']==41,'Wrong actual992+41 continuation scope')
        need(all(v is not None and v.is_file()for v in[a.supervisor,a.resource_plan,a.stdout,a.stderr,a.unit_properties]),'Actual completed owned resource evidence required')
        s=load(a.supervisor);plan=load(a.resource_plan);props=load(a.unit_properties)
        need(s['status']=='COMPLETE_CHILD' and type(s['returncode'])is int and s['returncode']==0 and s['stop_reason']is None,'Owned continuation did not complete successfully')
        need(type(s['seconds'])in[int,float]and math.isfinite(s['seconds'])and s['seconds']>0,'Invalid actual continuation time')
        need(s['stdout_sha256']==sha(a.stdout) and s['stderr_sha256']==sha(a.stderr),'Actual supervisor log association differs')
        need(not a.stderr.read_bytes() and a.stdout.read_text().endswith('PASS_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV\n'),'Missing actual controller completion marker or stderr diagnostic')
        need(s['source_cold_lineage']is True and s['monolithic_fresh_source_cold']is False,'Supervisor mislabeled resumed source lineage')
        need(plan['source_controller_sha256']==s['controller_sha256']==CONTROLLER_SHA,'Supervisor/controller source association differs')
        expected=['python3','-u',str(HERE/'resume_fft_dag_source_cold.py'),'--context',str(a.context),'--candidate',str(a.candidate.resolve()),'--prefix',p['original_prefix'],'--run',str(run),'--workers','12','--worker-memory-gib','256']
        need(plan['command']==expected and p['workers']==12 and p['per_compiler_AS_bytes']==256*2**30,'Actual continuation compiler/virtual limits differ')
        need(plan['aggregate_physical_memory_cap_bytes']==300*2**30 and plan['per_process_virtual_AS_cap_bytes']==256*2**30 and plan['virtual_limits_are_not_RAM_commitments']is True,'Virtual/physical resource distinction differs')
        need(plan['available_RAM_bytes']>=2**40 and plan['free_disk_bytes']>=2**40 and plan['owned_scratch_bytes']<270*2**30,'Actual independent resource admission failed')
        need(plan['host_reserve_bytes']==256*2**30 and plan['scratch_stop_bytes']==290*2**30,'Host/scratch reserve differs')
        before=s['before'];after=s['final'];unit='ivy-n24-source-cold-lineage-resume.service'
        need(before==plan['before']and before['path']==after['path']and before['path'].startswith('/sys/fs/cgroup/')and before['path'].endswith('/'+unit),'Owned cgroup identity differs')
        first=memory_events(before['memory.events']);last=memory_events(after['memory.events']);need(set(first)==set(last),'Owned cgroup event fields differ')
        delta={k:last[k]-first[k]for k in first};need(all(v>=0 for v in delta.values())and delta['oom']==delta['oom_kill']==0,'Actual owned OOM event occurred or counters decreased')
        if'oom_group_kill'in delta:need(delta['oom_group_kill']==0,'Actual owned group OOM kill occurred')
        actual=props['properties'];need(props['status']=='ACTUAL_OWNED_UNIT_PROPERTY_OBSERVATION_DURING_RUN'and props['unit']==unit and props['not_inferred_from_resource_plan']is True,'Actual independent unit properties required')
        need('/sys/fs/cgroup'+actual['ControlGroup']==before['path']and actual['MemoryMax']==str(300*2**30)and actual['MemorySwapMax']=='0'and actual['CPUQuotaPerSecUSec']=='12s','Actual physical/swap/CPU unit bounds differ')
        need(s['samples'],'Missing actual resource telemetry')
        for sample in s['samples']:
            need(sample['available_RAM_bytes']>=256*2**30 and sample['owned_scratch_bytes']<290*2**30 and sample['cgroup']['path']==before['path'],'Actual host/scratch/cgroup resource sample failed')
        resource=dict(actual_owned_memory_events_delta=delta,actual_OOM_not_inferred_from_success=True,
            sampled_cgroup_current_max_bytes=max(int(v['cgroup']['memory.current'])for v in s['samples']),sampled_peak_not_exact=True,
            wall_seconds=s['seconds'],supervisor_sha256=sha(a.supervisor),resource_plan_sha256=sha(a.resource_plan),unit_observation_sha256=sha(a.unit_properties))
    publish(a.output,dict(status='PASS_INDEPENDENT_FIXED_W4_FFT_SOURCE_COLD_LINEAGE_RESUME_KERNEL_ONLY',
        stages=r['stages'],N=r['N'],norm_numerator=r['norm_numerator'],modules=r['modules'],
        reused_successful_source_cold_modules=r['reused_successful_source_cold_modules'],freshly_compiled_modules=r['freshly_compiled_modules'],
        typed_claim_roots=r['audited_roots'],result_sha256=sha(run/'RESULT.json'),plan_sha256=sha(run/'PLAN.json'),
        validator_sha256=sha(Path(__file__)),source_cold=False,source_cold_lineage=True,full_C_source_first_PV_claimed=False,
        actual_resource_evidence=resource,toy_only=a.proof_only_toy))
    print('PASS independent exact FFT source-cold lineage; source-PV/ANT consumption is separate')


if __name__=='__main__':main()
