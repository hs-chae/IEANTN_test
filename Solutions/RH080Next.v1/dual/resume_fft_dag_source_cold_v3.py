#!/usr/bin/env python3
"""Additive nested continuation: preserve original + successfully checked later phases.
No original source, candidate, mathematical checker or prior outcome is rewritten.
"""
import argparse,concurrent.futures,math,os,re,shutil,subprocess,sys,time
from pathlib import Path
from reproduce_dual import context,need,publish,sha,load
from resume_fft_dag_source_cold import R,S,ORIGINAL_DRIVER_SHA,CONTEXT_HELPER_SHA,GENERIC,BAD,receipt,lean_command,link_checked,check_axioms
import fft_dag_nested_lineage_v3 as nested
from fft_dag_nested_lineage_v3 import validate_nested_lineage

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for arg in ['context','candidate','prefix','run']:ap.add_argument('--'+arg,type=Path,required=True)
    ap.add_argument('--continuation',type=Path,action='append',required=True)
    ap.add_argument('--nested-continuation',type=Path,required=True)
    ap.add_argument('--workers',type=int,default=12);ap.add_argument('--worker-memory-gib',type=int,default=300)
    ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args()
    need(1<=a.workers<=32 and 16<=a.worker_memory_gib<=300,'Bounded compiler resource parameters')
    need(not os.path.lexists(a.run),'Fresh resume destination required')
    a.run=a.run.resolve();a.prefix=a.prefix.resolve();a.candidate=a.candidate.resolve()
    c=context(a.context,R);state=validate_nested_lineage(a.prefix,a.candidate,a.context,c,a.continuation,a.nested_continuation)
    start=time.monotonic();controller_hash=sha(Path(__file__));oldplan_sha=sha(a.prefix/'PLAN.json');candidate_sha=sha(a.candidate/'PLAN.json')
    a.run.mkdir(parents=True);frozen=a.run/'sources';bank=a.run/'objects';frozen.mkdir();bank.mkdir()
    shutil.copyfile(Path(__file__),a.run/'resume_driver.executed.py');shutil.copyfile(a.prefix/'driver.executed.py',a.run/'driver.executed.py');shutil.copyfile(a.prefix/'producer.executed.py',a.run/'producer.executed.py')
    shutil.copyfile(a.prefix/'PLAN.json',a.run/'ORIGINAL_SOURCE_COLD_PLAN.json')
    rows=state['rows'];reused=state['successful'];routes={}
    for name,row in rows.items():link_checked(a.prefix/'sources'/row['file'],frozen/row['file'],row['sha256'])
    for row in state['proposal']['payloads']:link_checked(a.candidate/row['file'],frozen/row['file'],row['sha256'])
    for name,record in reused.items():
        object_path=Path(name.replace('.','/')+'.olean');link_checked(state['origins'][name]/'objects'/object_path,bank/object_path,record['object_sha256'])
        for ext in ['COMPILED.json','stdout','stderr','time']:
            source=state['origins'][name]/(name+'.'+ext);link_checked(source,a.run/(name+'.'+ext),sha(source))
        routes[name]=dict(kind='REUSED_VERIFIED_SOURCE_COLD_LINEAGE_PREFIX',compile_origin=str(state['origins'][name]),logical_compile_origin=str(state['logical_origins'][name]),phase=state['phases'][name],receipt_sha256=sha(state['origins'][name]/(name+'.COMPILED.json')),object_sha256=record['object_sha256'])
    plan=dict(status='FROZEN_V3_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV',nested_schema=3,continuation_helper_sha256=sha(Path(nested.__file__)),continuation_plans=state['continuation_plans'],original_successful_modules=state['original_successful_count'],inherited_continuation_modules=state['continuation_successful_count'],phase_counts=state['phase_counts'],sources=list(rows.values()),payloads=state['proposal']['payloads'],proposal=state['proposal'],
              original_prefix=str(a.prefix),original_logical_run=str(state['logical']),original_plan_sha256=oldplan_sha,original_controller_sha256=ORIGINAL_DRIVER_SHA,
              controller_sha256=controller_hash,context_helper_sha256=CONTEXT_HELPER_SHA,context_sha256=sha(a.context),compiler_sha256=c['compiler_sha256'],generic_dependencies=c['generic_dependencies'],
              candidate_plan_sha256=candidate_sha,workers=a.workers,per_compiler_AS_bytes=a.worker_memory_gib*2**30,
              source_cold=False,source_cold_lineage_resume=True,outside_application_object_cache_used=False,
              successful_prefix_modules=len(reused),fresh_modules_required=len(rows)-len(reused),routes=routes,incomplete_prior_receipts=state['incomplete'],
              immutable_snapshots_and_prefix_objects_hardlinked=True,aggregate_resource_supervision='Owner-provided independent bounded supervisor required for the large N24 run')
    publish(a.run/'PLAN.json',plan)
    if a.prepare_only:print('PREPARED_LINEAGE_ONLY_NOT_ACCEPTED',len(reused),len(rows)-len(reused),flush=True);return
    env=dict(os.environ,LEAN_PATH=str(bank)+':'+c['generic_lean_path']);done=dict(reused);pending=set(rows)-set(done);running={}
    def compile_one(name):
        row=rows[name];source=frozen/row['file'];obj=bank/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        command=lean_command(c['compiler'],a.run,row);out=a.run/(name+'.stdout');err=a.run/(name+'.stderr');tm=a.run/(name+'.time')
        actual=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(a.worker_memory_gib*2**30),'--stack='+str(256*2**20),'--',*command];tick=time.monotonic()
        with out.open('x')as stdout,err.open('x')as stderr:
            result=subprocess.run(actual,env=env,stdout=stdout,stderr=stderr)
        timing=tm.read_text();rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
        record=dict(module=name,returncode=result.returncode,seconds=time.monotonic()-tick,peak_RSS_KiB=int(rss[1])if rss else None,source_sha256=sha(source),command=command,resource_command=actual,
                    stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm))
        if obj.is_file():record['object_sha256']=sha(obj)
        publish(a.run/(name+'.COMPILED.json'),record)
        receipt(a.run,a.run,row,c['compiler'],True);return record
    try:
        with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers)as pool:
            while pending or running:
                ready=sorted(name for name in pending if all(dep.split('.')[0]in GENERIC or dep in done for dep in rows[name]['imports']))
                while ready and len(running)<a.workers:
                    name=ready.pop(0);pending.remove(name);running[pool.submit(compile_one,name)]=name
                need(bool(running),'Resume dependency scheduling stalled')
                finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
                for future in finished:
                    name=running.pop(future);done[name]=future.result();routes[name]=dict(kind='FRESH_COMPILE_AFTER_VALIDATED_PREFIX')
                    progress=dict(completed=len(done),total=len(rows),reused_prefix=len(reused),fresh_completed=len(done)-len(reused),latest=name)
                    temporary=a.run/'PROGRESS.pending';temporary.write_text(__import__('json').dumps(progress)+'\n');temporary.replace(a.run/'PROGRESS.json');print(progress,flush=True)
        need(len(done)==len(rows),'Incomplete whole fixed mathematical DAG')
        for name,row in rows.items():receipt(a.run,state['logical_origins'][name]if name in reused else a.run,row,c['compiler'],True)
        audits=check_axioms(a.run,state)
        for row in state['proposal']['payloads']:need(sha(frozen/row['file'])==row['sha256'],'Final original literal data differs')
        need(sha(a.prefix/'PLAN.json')==oldplan_sha and sha(a.candidate/'PLAN.json')==candidate_sha,'Original lineage/candidate changed during resume')
        need(sha(Path(__file__))==controller_hash,'Resume controller changed')
        need(sha(Path(nested.__file__))==plan['continuation_helper_sha256'],'Nested lineage helper changed')
        for parent in state['continuation_plans']:need(sha(Path(parent['path'])/'PLAN.json')==parent['plan_sha256'],'Prior continuation plan changed')
        publish(a.run/'AXIOM_AUDIT.json',dict(status='PASS_UNCHANGED_ORIGINAL_TYPED_CLAIM_AND_AXIOM_AUDIT',roots=audits))
        publish(a.run/'RESULT.json',dict(status='PASS_W4_INTEGER_FFT_V3_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV',nested_schema=3,reused_original_source_cold_modules=state['original_successful_count'],reused_prior_continuation_modules=state['continuation_successful_count'],phase_counts=state['phase_counts'],continuation_plans=state['continuation_plans'],stages=state['proposal']['stages'],N=state['proposal']['n'],norm_numerator=state['proposal']['norm_numerator'],modules=len(done),
                 reused_successful_source_cold_modules=len(reused),freshly_compiled_modules=len(done)-len(reused),seconds=time.monotonic()-start,audited_roots=len(audits),routes=routes,
                 max_individual_RSS_KiB=max(record['peak_RSS_KiB']for record in done.values()),plan_sha256=sha(a.run/'PLAN.json'),original_plan_sha256=oldplan_sha,candidate_plan_sha256=candidate_sha,
                 source_cold=False,source_cold_lineage_resume=True,outside_application_object_cache_used=False,original_run_and_outcome_preserved=True,full_original_C_FFT_PV=False,
                 numerical_parameters_and_checker_mathematics_unchanged=True,aggregate_resources_and_OOM='See independent owned supervisor receipt; never inferred from success'))
        print('PASS_V3_NESTED_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV',flush=True)
    except BaseException as error:
        publish(a.run/'FAILURE.json',dict(status='NO_ACCEPTANCE',error=str(error),reused_prefix=len(reused),fresh_completed=len(done)-len(reused),seconds=time.monotonic()-start));raise


if __name__=='__main__':main()
