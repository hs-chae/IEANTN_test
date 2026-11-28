#!/usr/bin/env python3
"""Strict completed681-source finite-Fap gate, with owned cgroup evidence.
Read-only Git in the pinned generic-context verifier is explicitly authorized.
"""
from __future__ import annotations
import argparse,hashlib,json,math,os,re
from pathlib import Path
import resume_final_fap_source_cold_v2 as core
from compile_verified_batch import atomic,imports,need
HERE=Path(__file__).resolve().parent
PINS={'reproduce_final_fap_source_v2.py': 'af4c6f564b78642a405f18d194f679f975c0f8655a3899d7d7976221be82b05d', 'reproduce_final_fap_source_cold_v2.py': '01c75c63018220e49082b1c9c6e68b86479afe7cd9e739e8bf786723acd12f64', 'resume_final_fap_source_cold_v2.py': 'bdcaabdf2c1e7690c122b976fdb780ba5ac5281bc091ff88b5733f0feca8e3b3', 'final_fap_source_resume_v2.py': '72e06dfcdb3df9767a4b3ffcf9d665a2f4e2f54d3c2acde309da7753cb031728', 'compile_verified_batch.py': '2de2fcbf30606ecb258423d4b27727c36d7d3beb55949d5b5850cd656515efcf', 'final_fap_source_data_v2.py': '33f1598308fc712e8e062943d8dde40d1fb7f3d0d2e6d8c185b56a0f5af12594', 'evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json': '8754df71c8e5261c4126e0f29a7c90be595a19f53e4977e15a4ef8f1ecbb5422'}
CONTEXT_SHA='88a89fb62356f9ac34abaa4f50a32584a75a33bd8ad23aae92cf07965f344319'
C_PINS={"fap_fft_recursive.c":"c1b958953998c2b655a40b3e25689a33c28d36ab2d145fdb22547a47ff5aa558","w4_fft_recursive.c":"0c9e29db9bbfacd8ed049dc8e4b2a2f18d8ae146c1d0e4dd47a93cd89b80e22b"}
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):
    h=hashlib.sha256()
    with p.open('rb')as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def strict(p):
    def pairs(items):
        d={}
        for k,v in items:need(k not in d,'duplicate JSON key '+k);d[k]=v
        return d
    def bad(v):raise ValueError('nonfinite JSON '+v)
    return json.loads(p.read_text(encoding='utf-8'),object_pairs_hook=pairs,parse_constant=bad)
def positive(v):return type(v)in[int,float]and math.isfinite(v)and v>0
def events(text):
    result={}
    for line in text.splitlines():
        parts=line.split();need(len(parts)==2 and parts[0]not in result and parts[1].isdigit(),'malformed cgroup memory.events')
        result[parts[0]]=int(parts[1])
    need({'oom','oom_kill'}<=set(result),'missing actual OOM counters');return result
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for flag in ['run','supervisor','prefix-supervisor','execution-plan','driver-stdout','driver-stderr','output']:ap.add_argument('--'+flag,required=True,type=Path)
    ap.add_argument('--owned-unit',required=True)
    a=ap.parse_args();b=a.run
    need(not a.output.exists(),'fresh atomic acceptance output required')
    need((b/'RESULT.json').is_file(),'missing completed atomic RESULT')
    need(a.supervisor.is_file(),'missing completed owned supervisor')
    frozen={str(p):sha(p)for p in [b/'PLAN.json',b/'RESULT.json',a.supervisor,a.prefix_supervisor,a.execution_plan]}
    p=strict(b/'PLAN.json');r=strict(b/'RESULT.json');supervisor=strict(a.supervisor);execution=strict(a.execution_plan)
    need(r['status']=='PASS_COMPLETE_FINITE_FAP_FULL_MAIN_ANT_SOURCE_COLD_SAME_EXPERIMENT_RESUME_V2','wrong completed finite-Fap result status')
    need(supervisor['status']=='COMPLETE_CHILD'and type(supervisor['exitcode'])is int and supervisor['exitcode']==0,'source-cold supervisor did not complete successfully')
    need(positive(supervisor['seconds']),'invalid supervisor elapsed time')
    need(sha(a.driver_stdout)==supervisor['stdout_sha256']and sha(a.driver_stderr)==supervisor['stderr_sha256'],'owned supervisor log identity')
    need(not a.driver_stderr.read_bytes(),'source-cold supervisor stderr')
    need(a.driver_stdout.read_text().endswith('PASS same-experiment finite Fap actual-main source-cold resume:357 reused+324 fresh=681;34 literal data files\n'),'missing actual driver completion marker')
    before=supervisor['before'];after=supervisor['final'];owned=before['path']
    need(owned==after['path']==execution['before']['path']and owned!='/'and owned.endswith('/'+a.owned_unit) and a.owned_unit=='ivy-final-fap-source-cold-resume-v2.service','wrong owned cgroup identity')
    need(before==execution['before'],'supervisor/execution-plan initial cgroup association')
    first=events(before['memory.events']);last=events(after['memory.events']);need(set(first)==set(last),'cgroup event population changed')
    delta={k:last[k]-first[k]for k in first};need(all(v>=0 for v in delta.values()),'cgroup counters decreased')
    need(all(delta.get(k,0)==0 for k in ['oom','oom_kill','oom_group_kill']),'actual owned OOM events occurred')
    priorSupervisor=strict(a.prefix_supervisor)
    need(priorSupervisor['status']=='FAILED_CHILD' and priorSupervisor['exitcode']==1,'prefix stop lineage differs')
    need(priorSupervisor['before']['path']==priorSupervisor['final']['path'] and priorSupervisor['before']['path'].endswith('/ivy-final-fap-full-main-source-cold-v2.service'),'prefix owned cgroup differs')
    priorStart=events(priorSupervisor['before']['memory.events']);priorEnd=events(priorSupervisor['final']['memory.events'])
    priorDelta={k:priorEnd[k]-priorStart[k]for k in priorStart}
    need(all(v>=0 for v in priorDelta.values()) and all(priorDelta.get(k,0)==0 for k in ['oom','oom_kill','oom_group_kill']),'prefix actual OOM event occurred')
    need(r['OOM_events']is None and r['OOM_event_counter_not_inferred_from_success']is True,'child must not invent actual OOM counters')
    for name,digest in PINS.items():need(sha(HERE/name)==digest,'reviewed final source-cold controller/input changed '+name)
    need(p['controller_sha256']==PINS['resume_final_fap_source_cold_v2.py']and p['helper_sha256']==PINS['compile_verified_batch.py'],'controller/helper plan association')
    need(execution['controller_sha256']==PINS['resume_final_fap_source_cold_v2.py'] and execution['helper_sha256']==PINS['final_fap_source_resume_v2.py'],'supervised resume controller/helper association')
    need(execution['no_external_application_cache'] is True and execution['reused_same_experiment_source_cold_modules']==357 and execution['fresh_modules_expected']==324,'supervised resume cache/fresh scope differs')
    need(execution['RAM_available_bytes']>=2**40 and execution['free_disk_bytes']>=2**40 and execution['owned_scratch_bytes']<270*2**30,'supervised resume resource admission differs')
    need(p['source_cold']is True and p['application_object_fallback']is False and r['source_cold']is True and r['application_object_fallback']is False,'not complete fresh source-only execution')
    need(p['literal_FFT_DAG_recompiled']is True and r['literal_FFT_DAG_recompiled']is True and r['fixed_literal_certificate_and_ANT_pending']is False,'literal FFT or final ANT still pending')
    inputData=strict(HERE/'evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json');need(inputData['kind']=='SOURCE_AND_LITERAL_DATA_IDENTITIES_NO_APPLICATION_PROOF_CACHE' and inputData['schema_version']==2 and inputData['modules']==681 and len(inputData['sources'])==681,'wrong finite-Fap portable scope')
    expected={x['module']:x for x in inputData['sources']};need(len(expected)==681,'duplicate portable compiler identity')
    names=[x['module']for x in p['source_rows']];need(len(names)==681 and len(set(names))==681 and set(names)==set(expected),'omitted/extra/collapsed source identity')
    need(p['schema_version']==r['schema_version']==2 and p['literal_data_files']==r['literal_data_files']==34 and p['literal_data_bytes']==r['literal_data_bytes']==104208750,'missing exact literal data scope')
    need(p['literal_data_helper_sha256']==PINS['final_fap_source_data_v2.py'],'literal data helper lineage')
    need((b/'LITERAL_DATA.json').is_file(),'missing staged literal data manifest')
    frozen[str(b/'LITERAL_DATA.json')]=sha(b/'LITERAL_DATA.json')
    dataManifest=strict(b/'LITERAL_DATA.json')
    need(dataManifest['schema_version']==2 and dataManifest['literal_data_are_untrusted_proposals'] is True and dataManifest['rows']==p['literal_data'] and sha(b/'LITERAL_DATA.json')==p['literal_data_manifest_sha256']==r['literal_data_manifest_sha256'],'literal staged/final manifest association')
    expectedData=[]
    for item in inputData['data']:
        row={k:v for k,v in item.items()if k!='path'};row['source_origin']=str((HERE.parents[2]/item['path']).resolve());expectedData.append(row)
    expectedData.sort(key=lambda x:x['destination'])
    need([{k:v for k,v in x.items()if k!='snapshot'}for x in p['literal_data']]==expectedData,'literal source identities differ from frozen portable inputs')
    need(p['same_experiment_source_cold_resume'] is True and r['same_experiment_source_cold_resume'] is True and p['reused_source_cold_modules']==r['reused_source_cold_modules']==357 and p['fresh_source_cold_modules']==r['fresh_source_cold_modules']==324,'wrong357/324 same-experiment scope')
    need(p['resume_helper_sha256']==PINS['final_fap_source_resume_v2.py'] and p['resume_manifest_sha256']==r['resume_manifest_sha256']==sha(b/'REUSED_SOURCE_COLD_PREFIX.json'),'resume manifest/helper lineage differs')
    resumeManifest=strict(b/'REUSED_SOURCE_COLD_PREFIX.json');need(execution['prefix_plan_sha256']==resumeManifest['prefix_plan_sha256'],'supervised prefix source-cold plan association differs');reusedNames={x['module']for x in resumeManifest['rows']};need(len(reusedNames)==357,'wrong reused module population')
    need(r['modules']==681 and type(r['modules'])is int,'wrong completed source population')
    need(r['plan_sha256']==sha(b/'PLAN.json'),'completed plan hash differs')
    need(p['workers']==r['workers']and 1<=p['workers']<=4 and p['worker_AS_bytes']==r['worker_AS_bytes'],'worker allowance association')
    need(p['workers']*p['worker_AS_bytes']==p['aggregate_AS_allowance_bytes']<=300*2**30,'aggregate memory allowance exceeds scope')
    need(p['host_reserve_bytes']==256*2**30 and p['admission_MemAvailable_bytes']>=max(2**40,p['aggregate_AS_allowance_bytes']+p['host_reserve_bytes']),'host RAM admission reserve')
    need(p['admission_free_disk_bytes']>=2**40 and p['scratch_stop_bytes']<=290*2**30,'disk/scratch admission reserve')
    need(not r['resource_failures'],'source-cold resource failure')
    need(r['minimum_MemAvailable_bytes']>=p['host_reserve_bytes']and r['campaign_scratch_max_sampled_bytes']<p['scratch_stop_bytes'],'sampled host/scratch reserve failed')
    need(r['sampled_group_RSS_not_exact_peak']is True,'sampled RSS mislabeled exact')
    inventory=strict(Path(p['inventory']));need(inventory['portable_inputs_sha256']==PINS['evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json']and inventory['portable_controller_sha256']==PINS['reproduce_final_fap_source_v2.py'],'portable inventory lineage')
    need(len(inventory['full_dependency_cone'])==681,'inventory scope changed')
    need(inventory['schema_version']==2 and inventory['literal_data_helper_sha256']==PINS['final_fap_source_data_v2.py'] and inventory['literal_data']==expectedData,'literal inventory lineage differs')
    context=strict(Path(p['context']));need(sha(Path(p['context']))==p['context_sha256']==CONTEXT_SHA,'approved pinned context association')
    firstRow=p['source_rows'][0];logicalRun=Path(firstRow['snapshot']).parents[len(firstRow['module'].split('.'))-1].parent
    expectedDriver=['python3',str(HERE/'resume_final_fap_source_cold_v2.py'),'--context',p['context'],'--prefix',resumeManifest['prefix'],'--run',str(logicalRun),'--scratch-root',p['scratch_root'],'--workers',str(p['workers']),'--worker-memory-gib',str(p['worker_AS_bytes']//2**30)]
    need(execution['command']==expectedDriver,'actual supervised portable-driver command differs')
    records={x['module']:x for x in r['commands']};need(len(r['commands'])==681 and set(records)==set(expected),'missing/duplicate actual compiler route')
    repo=HERE.parents[2];peak=[];attempts=[]
    for row in p['source_rows']:
        n=row['module'];origin=(repo/expected[n]['path']).resolve()
        need(origin.is_relative_to(repo)and str(origin)==row['origin']and row['source_sha256']==expected[n]['sha256'],'written source identity differs '+n)
        need(row['imports']==imports(origin),'actual import inventory differs '+n)
        q=strict(b/(n+'.COMPILED.json'));attempt=strict(b/(n+'.ATTEMPT.json'))
        need(q==records[n]and {k:v for k,v in q.items()if k!='object_sha256'}==attempt,'compiler/attempt/final receipt association '+n)
        need(q['exitcode']==0 and positive(q['seconds']),'failed actual compiler '+n)
        logical=Path(row['snapshot']).parents[len(n.split('.'))-1].parent
        expectedCommand=['/usr/bin/time','-v','-o',str(logical/'logs'/(n+'.time')),'prlimit','--as='+str(p['worker_AS_bytes']),'--stack='+str(256*2**20),'--',context['compiler'],'-j1','--root='+str(logical/'source'),'-o',str(logical/'objects'/(n.replace('.','/')+'.olean')),row['snapshot']]
        if n in reusedNames:
            originalReceipt=Path(resumeManifest['prefix'])/(n+'.COMPILED.json')
            need(q==strict(originalReceipt),'reused compiler provenance differs '+n)
        else:
            need(q['command']==expectedCommand,'actual compiler flags/source/cache context differs '+n)
        timing=(b/'logs'/(n+'.time')).read_text();rss=re.findall(r'^\s*Maximum resident set size \(kbytes\):\s*(\d+)\s*$',timing,re.M);exitStatus=re.findall(r'^\s*Exit status:\s*(-?\d+)\s*$',timing,re.M)
        need(len(rss)==1 and len(exitStatus)==1 and exitStatus[0]=='0'and 'Command terminated by signal'not in timing,'compiler resource completion '+n);peak.append(int(rss[0])*1024)
        attempts.append(n)
    need(r['peak_compiler_child_RSS_bytes']==max(peak),'actual compiler RSS aggregate differs')
    samples=strict(b/'SAMPLED_RESOURCES.json');need(samples['sampled_not_exact_peak']is True and samples['samples'],'missing sampled resource evidence')
    ss=samples['samples'];need(r['sampled_group_RSS_max_bytes']==max(x['RSS_bytes']for x in ss)and r['minimum_MemAvailable_bytes']==min(x['MemAvailable_bytes']for x in ss)and r['campaign_scratch_max_sampled_bytes']==max(x['campaign_scratch_bytes']for x in ss),'sampled resource summary association')
    for name,digest in C_PINS.items():need(sha(HERE/'fft'/name)==digest,'actual preserved C differs '+name)
    os.environ['GIT_OPTIONAL_LOCKS']='0'
    need(core.verify(b)==681,'base strict source-cold validation scope differs')
    finalAudit=(b/'logs/FFTFapMainAudit.stdout').read_text();axes=re.findall(r'^FAP_FULL_MAIN_ANT_AUDIT_ROOT (\S+) axioms=\[([^\]]*)\] closure=(\d+)$',finalAudit,re.M)
    need([x[0]for x in axes]==['RH080Next.FFTPV.FapMain.source_fap_'+x+'_full'for x in ['08','074','075']],'wrong actual full-main ANT root population')
    for _,axioms,_ in axes:need({x.strip()for x in axioms.split(',')if x.strip()}<=ALLOWED,'new final ANT axiom')
    for path,digest in frozen.items():need(sha(Path(path))==digest,'completion evidence changed during acceptance')
    result=dict(status='PASS_INDEPENDENT_COMPLETE_FINITE_FAP_MAIN_ANT_SAME_EXPERIMENT_SOURCE_COLD_RESUME',run=str(b),modules=681,reused_source_cold_modules=357,fresh_source_cold_modules=324,all681_fresh_this_phase=False,actual_prefix_memory_events_delta=priorDelta,source_cold=True,application_object_fallback=False,literal_N17_FFT_recompiled=True,literal_data_files=34,literal_data_bytes=104208750,literal_data_manifest_sha256=p['literal_data_manifest_sha256'],final_ANT_roots=3,model='selected exact C source/grammar/operational main/logical stdio; generic compiler/runtime/flush/OS/hardware contracts remain',actual_owned_memory_events_delta=delta,OOM_events_inferred_from_success=False,supervisor_sha256=sha(a.supervisor),result_sha256=sha(b/'RESULT.json'),plan_sha256=sha(b/'PLAN.json'),validator_sha256=sha(Path(__file__)),reviewed_source_pins=PINS,source_first_scope='actual main+all norm failure choices+real arithmetic+postnorm+all3 original finite ANT conclusions; no N24 W4 claim')
    atomic(a.output,result);print(json.dumps(dict(status=result['status'],modules=681,actual_OOM_delta=delta,receipt=str(a.output),sha256=sha(a.output))))
if __name__=='__main__':main()
