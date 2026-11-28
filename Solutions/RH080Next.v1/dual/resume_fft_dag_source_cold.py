#!/usr/bin/env python3
"""Resume one pinned FFT DAG's validated source-cold lineage.

Only successful receipts from the specified original source-cold run are reused.
Their objects and immutable source/data snapshots are hardlinked, never copied.
The result distinguishes that prefix from fresh compilation. This is kernel
certificate verification, not by itself source-first C PV. The original run,
controller, mathematical checker, candidate and outcomes remain unchanged.
"""
import argparse,concurrent.futures,math,os,re,shutil,subprocess,sys,time
from pathlib import Path
from reproduce_dual import context,need,publish,sha,load
R=Path(__file__).resolve().parents[3]
S=R/'Solutions/RH080Next.v1'
ORIGINAL_DRIVER_SHA='d8331f3cf82fdeb9f7bc3e0501bc602d27bf8cc5f54c6e2ec11507486a9483a4'
CONTEXT_HELPER_SHA='bd46aa86253e5e079087bf9260c93015eb63063159a8bb2bbebac9382ea1f122'
GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets'}
BAD=re.compile(r'PANIC|error(?:\([^)]*\))?:|fatal error|sorryAx',re.I)
SOURCE_BAD=re.compile(r'^\s*(?:axiom|opaque|sorry|admit)\b|\bnative_decide\b',re.M)
ALLOWED={'propext','Classical.choice','Quot.sound'}


def fixed_claim(proposal):
    """Exactly the original v2 checker-owned typed consumer, unchanged."""
    stages=proposal['stages'];ns=f'W4DAG{stages}';fixed='RH080Next.FFT.IntegerModel'
    lines=[f'import {proposal["final_module"]}','set_option maxRecDepth 2000000','set_option maxHeartbeats 0','set_option Elab.async false','noncomputable section',f'namespace W4ClaimAudit{stages}']
    lines += [f'theorem execution : {fixed}.ExecutionTrace {ns}.stages ({fixed}.W4.input {2**stages}) {stages} 0 1 {ns}.output := {ns}.complete_execution',f'theorem seed_exact : {ns}.seed={fixed}.root {2**stages} := by decide +kernel',f'theorem twiddle : {fixed}.TwiddleTrace ({fixed}.root {2**stages}) ({fixed}.unit,0) ({ns}.stages {stages}).tail := by\n  rw [←seed_exact]\n  exact {ns}.global_twiddle_trace',f'theorem lengths : ∀ t<{stages}, ({ns}.stages (t+1)).length=2^t := {ns}.stage_lengths',f'theorem top_shape : ∃ tail, {ns}.stages {stages}=({fixed}.unit,0)::tail := ⟨{ns}.topTail, {ns}.top_shape⟩',f'theorem numerator : {fixed}.W4.normFromOutput {2**stages} {ns}.output={proposal["norm_numerator"]} := {ns}.numerator_checked']
    for stage in range(1,stages):
        lines.append(f'theorem step{stage:02} : {fixed}.EvenTrace ({ns}.stages {stage+1}) ({ns}.stages {stage}) := {ns}.decimation{stage:02}')
    roots=['execution','seed_exact','twiddle','lengths','top_shape','numerator']+[f'step{stage:02}'for stage in range(1,stages)]
    lines += [f'#print axioms {root}'for root in roots]+[f'end W4ClaimAudit{stages}']
    return '\n'.join(lines)+'\n',roots


def imports(path):
    return [name for line in path.read_text().splitlines()if line.startswith('import ')
            for name in line[7:].split('--',1)[0].split()]


def finite_positive(value):
    return type(value)in[int,float]and math.isfinite(value)and value>0


def lean_command(compiler,logical_run,row):
    return [compiler,'-j1','-R',str(logical_run/'sources'),'-o',
            str(logical_run/'objects'/(row['module'].replace('.','/')+'.olean')),
            str(logical_run/'sources'/row['file'])]


def receipt(run,logical_run,row,compiler,require_success=True):
    name=row['module'];p=run/(name+'.COMPILED.json');record=load(p)
    need(record['module']==name and type(record['returncode'])is int,'Invalid compiler identity/status '+name)
    need(record['command']==lean_command(compiler,logical_run,row),'Actual compiler/context/flags differ '+name)
    need(record['source_sha256']==row['sha256']==sha(run/'sources'/row['file']),'Receipt source differs '+name)
    need(finite_positive(record['seconds']),'Invalid actual elapsed time '+name)
    for ext in ['stdout','stderr','time']:
        need(record[ext+'_sha256']==sha(run/(name+'.'+ext)),'Compiler log/time differs '+name)
    timing=(run/(name+'.time')).read_text()
    if require_success:
        need(record['returncode']==0,'Unsuccessful receipt cannot be reused '+name)
        need(BAD.search((run/(name+'.stdout')).read_text()+'\n'+(run/(name+'.stderr')).read_text())is None,'Strict compiler diagnostic '+name)
        need('Command terminated by signal'not in timing and re.search(r'Exit status:\s*0\s*$',timing)is not None,'Compiler did not finish '+name)
        peak=re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
        need(len(peak)==1 and type(record['peak_RSS_KiB'])is int and record['peak_RSS_KiB']==int(peak[0])>0,'Actual peakRSS differs '+name)
        need(record['object_sha256']==sha(run/'objects'/(name.replace('.','/')+'.olean')),'Accepted object differs '+name)
    return record


def validate_prefix(prefix,candidate,context_path,c):
    original=S/'dual/reproduce_fft_dag_v2.py'
    need(sha(original)==ORIGINAL_DRIVER_SHA==sha(prefix/'driver.executed.py'),'Original source-cold driver identity differs')
    need(sha(S/'dual/reproduce_dual.py')==CONTEXT_HELPER_SHA,'Pinned context helper differs')
    plan=load(prefix/'PLAN.json');proposal=load(candidate/'PLAN.json')
    need(plan['status']=='FROZEN_SOURCE_COLD_W4_INTEGER_FFT_DAG_NOT_C_PV' and plan['application_object_fallback']is False,'Not an original source-cold lineage')
    need(plan['controller_sha256']==ORIGINAL_DRIVER_SHA and plan['context_sha256']==sha(context_path),'Original exact controller/context differs')
    need(plan['compiler_sha256']==c['compiler_sha256'] and plan['generic_dependencies']==c['generic_dependencies'],'Original compiler/generic dependency identity differs')
    need(plan['candidate_plan_sha256']==sha(candidate/'PLAN.json') and plan['proposal']==proposal,'Candidate or mathematics changed')
    need(proposal['status']=='UNTRUSTED_W4_DAG_PROPOSAL_NOT_PROOF_NOT_PV','Wrong original candidate status')
    stages=proposal['stages'];need(type(stages)is int and 13<=stages<=24 and proposal['n']==2**stages,'Wrong original grid')
    need(proposal['namespace']==f'W4DAG{stages}' and proposal['final_module']==f'W4D{stages}Final','Changed original mathematical names')
    need(proposal['input_sha256']=='61f745f27018ea5addbb01c1d583b128b2639b0f101d764136c98c26983c5521','Original coefficients changed')
    if stages==24:need(proposal['norm_numerator']==7813568381279800,'Original N24 numerical claim changed')
    producer=S/'dual/produce_fft_dag_certificate.py'
    need(sha(producer)==proposal['producer_sha256']==sha(prefix/'producer.executed.py'),'Original numerical producer changed')
    generated={}
    for item in proposal['modules']:
        file=item['file'];name=file.removesuffix('.lean')
        need(Path(file).name==file and file.endswith('.lean')and re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*',name)is not None and name not in generated,'Duplicate/invalid generated module')
        need(sha(candidate/file)==item['sha256'],'Original generated source differs '+name);generated[name]=item
    need(proposal['final_module']in generated,'Missing original final mathematical consumer')
    need(plan['payloads']==proposal['payloads'],'Original literal input population differs')
    seen=set()
    for item in proposal['payloads']:
        file=item['file'];need(Path(file).name==file and file.endswith('.csv')and file not in seen,'Invalid/duplicate original literal data');seen.add(file)
        need(type(item['bytes'])is int and item['bytes']>0,'Invalid literal byte count')
        for path in [candidate/file,prefix/'sources'/file]:
            need(path.stat().st_size==item['bytes'] and sha(path)==item['sha256'],'Original literal data changed '+file)
    rows={};audit_name=f'W4D{stages}ClaimAudit';claim_text,roots=fixed_claim(proposal)
    for row in plan['sources']:
        name=row['module'];need(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',name)is not None and name not in rows,'Duplicate/invalid original source identity')
        need(row['file']==name.replace('.','/')+'.lean','Original source destination differs')
        source=prefix/'sources'/row['file'];need(sha(source)==row['sha256'],'Frozen original source differs '+name)
        need(imports(source)==row['imports'] and SOURCE_BAD.search(source.read_text())is None,'Source imports/unapproved leaf differ '+name)
        if name==audit_name:
            need(source.read_text()==claim_text and row['imports']==[proposal['final_module']],'Checker-owned fixed claim differs')
            logical=Path(row['origin']).parent
            need(Path(row['origin']).name==audit_name+'.lean','Original checker source identity differs')
        elif name in generated:
            need(row['sha256']==generated[name]['sha256']and row['imports']==generated[name]['imports'],'Generated mathematical contract differs')
            need(Path(row['origin'])==candidate/generated[name]['file'],'Original candidate path differs')
        else:
            origins=[folder/(name.replace('.','/')+'.lean')for folder in[S/'dual',S/'pv/lean']]
            origins=[path for path in origins if path.is_file()]
            need(len(origins)==1 and origins[0]==Path(row['origin'])and sha(origins[0])==row['sha256'],'Foundation source identity differs '+name)
        rows[name]=row
    need(audit_name in rows and set(generated)<=set(rows),'Original full mathematical DAG omitted')
    need(all(dep.split('.')[0]in GENERIC or dep in rows for row in rows.values()for dep in row['imports']),'Original application dependency missing')
    required=set();active=set()
    def visit(name):
        if name in required or name.split('.')[0]in GENERIC:return
        need(name not in active,'Original dependency cycle');active.add(name)
        for dep in rows[name]['imports']:visit(dep)
        active.remove(name);required.add(name)
    for name in [*generated,audit_name]:visit(name)
    need(required==set(rows),'Extra/unreachable original source route')
    successful={};incomplete=[]
    for p in sorted(prefix.glob('*.COMPILED.json')):
        name=p.name.removesuffix('.COMPILED.json');need(name in rows,'Unknown prior receipt')
        raw=load(p)
        if raw.get('returncode')==0:
            successful[name]=receipt(prefix,logical,rows[name],c['compiler'],True)
        else:
            record=receipt(prefix,logical,rows[name],c['compiler'],False)
            incomplete.append(dict(module=name,prior_returncode=record['returncode'],prior_receipt_sha256=sha(p)))
    for name in successful:
        need(all(dep.split('.')[0]in GENERIC or dep in successful for dep in rows[name]['imports']),'Successful prefix lacks its own application dependency '+name)
    need(successful,'No verified source-cold prefix to resume')
    return dict(plan=plan,proposal=proposal,rows=rows,successful=successful,incomplete=incomplete,logical=logical,audit=audit_name,claim_roots=roots)


def link_checked(source,target,digest):
    need(sha(source)==digest,'Immutable link source changed')
    target.parent.mkdir(parents=True,exist_ok=True);need(not os.path.lexists(target),'Fresh hardlink destination required')
    os.link(source,target)
    need(os.stat(source).st_ino==os.stat(target).st_ino and os.stat(source).st_dev==os.stat(target).st_dev,'Artifact was not hardlinked')
    need(sha(target)==digest,'Hardlinked snapshot changed')


def check_axioms(run,state):
    text=(run/(state['audit']+'.stdout')).read_text();audits=[];stages=state['proposal']['stages']
    for root in state['claim_roots']:
        full=f'W4ClaimAudit{stages}.'+root
        matches=re.findall(r"'"+re.escape(full)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
        need(len(matches)==1,'Missing exact original typed-claim axiom audit '+full)
        axes={v.strip()for v in matches[0].split(',')if v.strip()};need(axes<=ALLOWED,'Nonstandard final proof axiom '+full)
        audits.append(dict(root=full,axioms=sorted(axes)))
    return audits


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for arg in ['context','candidate','prefix','run']:ap.add_argument('--'+arg,type=Path,required=True)
    ap.add_argument('--workers',type=int,default=12);ap.add_argument('--worker-memory-gib',type=int,default=64)
    ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args()
    need(1<=a.workers<=32 and 16<=a.worker_memory_gib<=300,'Bounded compiler resource parameters')
    need(not os.path.lexists(a.run),'Fresh resume destination required')
    a.run=a.run.resolve();a.prefix=a.prefix.resolve();a.candidate=a.candidate.resolve()
    c=context(a.context,R);state=validate_prefix(a.prefix,a.candidate,a.context,c)
    start=time.monotonic();controller_hash=sha(Path(__file__));oldplan_sha=sha(a.prefix/'PLAN.json');candidate_sha=sha(a.candidate/'PLAN.json')
    a.run.mkdir(parents=True);frozen=a.run/'sources';bank=a.run/'objects';frozen.mkdir();bank.mkdir()
    shutil.copyfile(Path(__file__),a.run/'resume_driver.executed.py');shutil.copyfile(a.prefix/'driver.executed.py',a.run/'driver.executed.py');shutil.copyfile(a.prefix/'producer.executed.py',a.run/'producer.executed.py')
    shutil.copyfile(a.prefix/'PLAN.json',a.run/'ORIGINAL_SOURCE_COLD_PLAN.json')
    rows=state['rows'];reused=state['successful'];routes={}
    for name,row in rows.items():link_checked(a.prefix/'sources'/row['file'],frozen/row['file'],row['sha256'])
    for row in state['proposal']['payloads']:link_checked(a.candidate/row['file'],frozen/row['file'],row['sha256'])
    for name,record in reused.items():
        object_path=Path(name.replace('.','/')+'.olean');link_checked(a.prefix/'objects'/object_path,bank/object_path,record['object_sha256'])
        for ext in ['COMPILED.json','stdout','stderr','time']:
            source=a.prefix/(name+'.'+ext);link_checked(source,a.run/(name+'.'+ext),sha(source))
        routes[name]=dict(kind='REUSED_SUCCESSFUL_ORIGINAL_SOURCE_COLD_PREFIX',original_receipt_sha256=sha(a.prefix/(name+'.COMPILED.json')),object_sha256=record['object_sha256'])
    plan=dict(status='FROZEN_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV',sources=list(rows.values()),payloads=state['proposal']['payloads'],proposal=state['proposal'],
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
        for name,row in rows.items():receipt(a.run,state['logical']if name in reused else a.run,row,c['compiler'],True)
        audits=check_axioms(a.run,state)
        for row in state['proposal']['payloads']:need(sha(frozen/row['file'])==row['sha256'],'Final original literal data differs')
        need(sha(a.prefix/'PLAN.json')==oldplan_sha and sha(a.candidate/'PLAN.json')==candidate_sha,'Original lineage/candidate changed during resume')
        need(sha(Path(__file__))==controller_hash,'Resume controller changed')
        publish(a.run/'AXIOM_AUDIT.json',dict(status='PASS_UNCHANGED_ORIGINAL_TYPED_CLAIM_AND_AXIOM_AUDIT',roots=audits))
        publish(a.run/'RESULT.json',dict(status='PASS_W4_INTEGER_FFT_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV',stages=state['proposal']['stages'],N=state['proposal']['n'],norm_numerator=state['proposal']['norm_numerator'],modules=len(done),
                 reused_successful_source_cold_modules=len(reused),freshly_compiled_modules=len(done)-len(reused),seconds=time.monotonic()-start,audited_roots=len(audits),routes=routes,
                 max_individual_RSS_KiB=max(record['peak_RSS_KiB']for record in done.values()),plan_sha256=sha(a.run/'PLAN.json'),original_plan_sha256=oldplan_sha,candidate_plan_sha256=candidate_sha,
                 source_cold=False,source_cold_lineage_resume=True,outside_application_object_cache_used=False,original_run_and_outcome_preserved=True,full_original_C_FFT_PV=False,
                 numerical_parameters_and_checker_mathematics_unchanged=True,aggregate_resources_and_OOM='See independent owned supervisor receipt; never inferred from success'))
        print('PASS_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV',flush=True)
    except BaseException as error:
        publish(a.run/'FAILURE.json',dict(status='NO_ACCEPTANCE',error=str(error),reused_prefix=len(reused),fresh_completed=len(done)-len(reused),seconds=time.monotonic()-start));raise


if __name__=='__main__':main()
