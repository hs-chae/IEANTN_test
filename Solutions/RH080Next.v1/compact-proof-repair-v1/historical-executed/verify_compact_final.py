#!/usr/bin/env python3
"""Independent compact numerical proof gate. No source-first C-PV claim.
Strict JSON, exact source identities and compiler receipts, all original typed roots.
Production requires the actual completed unchanged owned supervisor and OOM0.
"""
import argparse,hashlib,json,math,os,re,sys,time
from pathlib import Path
D=Path('/data/ivy-rh080-next-20261125');S=D/'network/Solutions/RH080Next.v1'
sys.path.insert(0,str(S/'dual'))
import resume_fft_dag_source_cold as old
from reproduce_dual import context,need,sha,publish
EXPECTED = {13: {'source_hashes': {'W4D13FinalImportsProbe': '443465c649567375beb809c49d85d1c0e00772ff7df51eb7c6be12ed67dc9dea', 'TopShapeSymbolic': '121b1b44651f312abf569164f5117fe33ffb18d5ab3fc4f1c6f564fafee56726', 'NormSymbolic': 'dc3590afbf7a804cc8d033db03dbdda826f4575f6d2f59755a9c97d43500b333', 'W4D13Final': 'f9385eea472ff94103487ac94b64fe02dab5c354da6ace5b591bacdc323ad416', 'W4D13ClaimAudit': 'e8b3eca548be6a43769f50744859e388fff2276eadb1d537836ac34d1be23a65'}, 'original_final': '140018a66af046da2a0dd21078e38991fb0f320e5189a64035e707ccabce5c6d', 'original_audit': 'e8b3eca548be6a43769f50744859e388fff2276eadb1d537836ac34d1be23a65'}, 24: {'source_hashes': {'W4D24FinalImportsProbe': 'b71a86b259fecf43cb28bcf4809f10a4d22a674a89df5a70ef282d9f171931fd', 'TopShapeSymbolic': '121b1b44651f312abf569164f5117fe33ffb18d5ab3fc4f1c6f564fafee56726', 'NormSymbolic': 'dc3590afbf7a804cc8d033db03dbdda826f4575f6d2f59755a9c97d43500b333', 'W4D24Final': 'edd68a4f35cb9c5bc34385630683145c3782f8516d8ee87ab3b2fac42488667e', 'W4D24ClaimAudit': 'd950c97f4f95f8282a76f35baa435796aa8d09f282195efc0877221768829f67'}, 'original_final': '0580d2758c2908eb496518bf654df17163736019f4bfdeadad8dafa99df4da69', 'original_audit': 'd950c97f4f95f8282a76f35baa435796aa8d09f282195efc0877221768829f67'}}
OLD_HELPER_SHA = '04421c858331351ed4e2dbf3bd7e13c3bac10182fb2c14c852fd1567afb5afa8'
CONTROLLERS = {13: '7bdea5eef7035576766a339ea8b17c09e00fe64e6305a8f5365ea53ae5107395', 24: 'fed37e31d8de41d1f1a1611c8d50b43ba1e46f34e5e58686e450ea3e6320addb'}

SUP_SHA='03015a743b49c1cb840e2cb5e2a6c6d7e49be93b69aa244cf6f698b7dff74d56'
PAGE_SHA='b702ded5c9f73e2559bb3f1f3b5116f98dd0646fb60e816bff5617df6180cd9c'
ALLOWED={'propext','Classical.choice','Quot.sound'}
BAD=re.compile(r'PANIC|error(?:\([^)]*\))?:|fatal error|sorryAx|native_decide|Lean\.ofReduceBool',re.I)


def load(p):
    def pairs(items):
        result={}
        for k,v in items:
            need(k not in result,'Duplicate JSON key '+k)
            result[k]=v
        return result
    def bad(value):raise ValueError('Nonfinite JSON '+value)
    return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=bad)


def positive(x):
    return type(x)in[int,float]and math.isfinite(x)and x>0


def parse_events(text):
    rows=[line.split()for line in text.splitlines()]
    need(all(len(row)==2 for row in rows),'Invalid memory event row')
    need(len({row[0]for row in rows})==len(rows),'Duplicate memory event')
    result={k:int(v)for k,v in rows}
    need(set(result)>={'high','max','oom','oom_kill'}and all(v>=0 for v in result.values()),'Invalid counters')
    return result


def axes(stdout,expected=None):
    rows=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",stdout)
    rows += [(name,'')for name in re.findall(r"'([^']+)' does not depend on any axioms",stdout)]
    need(len({n for n,v in rows})==len(rows),'Duplicate actual axiom root')
    result={n:[x.strip()for x in v.split(',')if x.strip()]for n,v in rows}
    for name,names in result.items():need(set(names)<=ALLOWED,'Nonstandard/native axiom in '+name)
    if expected is not None:need(set(result)==set(expected),'Missing/extra original typed roots')
    return result


def verify_math(run,assembly_dir,ctxpath,toy):
    need(sha(Path(old.__file__))==OLD_HELPER_SHA,'Pinned inherited receipt checker changed')
    p=load(run/'PLAN.json');result=load(run/'RESULT.json');assembly=load(assembly_dir/'ASSEMBLY.json')
    stage=assembly['stage'];need(type(stage)is int and stage in[13,24],'Unsupported fixed stage')
    need((toy and stage==13)or(not toy and stage==24),'Explicit toy/production scope mismatch')
    need(p['status']=='PRIVATE_COMPACT_SOURCE_ASSOCIATED_PROOF_ONLY_REPAIR_NOT_NETWORK_ACCEPTANCE','Wrong compact plan')
    need(result['status']=='PASS_PRIVATE_COMPACT_SAME_PUBLIC_STATEMENTS_ORIGINAL_TYPED_AUDIT','No completed compact proof')
    need(p['stage']==result['stage']==stage and p['original_assembly']==assembly,'Assembly/result differs')
    need(result['plan_sha256']==sha(run/'PLAN.json'),'Final result refers to different plan')
    need(p['modules']==assembly['modules']and len(p['modules'])==result['modules']==5,'Wrong five actual compiler calls')
    fixed=EXPECTED[stage]
    need({r['module']:r['sha256']for r in p['modules']}==fixed['source_hashes'],'Reviewed exact proof-source identity differs')
    need(assembly['original_Final_sha256']==fixed['original_final']and assembly['original_ClaimAudit_sha256']==fixed['original_audit'],'Original written claims differ')
    need(assembly['proof_only_changed_declarations']==['top_shape','numerator_checked']and assembly['same_public_FQ_names_and_type_headers']is True and assembly['all_other_bodies_byte_unchanged']is True and assembly['original_typed_audit_byte_unchanged']is True,'Invalid proof-only scope')
    need(sha(Path(assembly['original_Final_source']))==fixed['original_final']and sha(Path(assembly['original_ClaimAudit_source']))==fixed['original_audit'],'Original source changed')
    if stage==24:
        need(assembly['generator_sha256']=='e04d714e7cc0d09c9d399cec36be2c007649bd07a3db1c9b3af4296480165fd2'and assembly['independently_pinned_original_ClaimAudit_sha256']==fixed['original_audit'],'Production audit source not independently pinned')
    need(p['context_sha256']==sha(ctxpath),'Exact compiler context changed')
    c=context(ctxpath,old.R);need(c['compiler_sha256']==p['compiler_sha256'],'Compiler changed')
    pins=p['source_pins'];need(len({r['path']for r in pins})==len(pins),'Duplicate actual source pin')
    for row in pins:need(sha(Path(row['path']))==row['sha256'],'Executed compact source changed')
    controllers=[r for r in pins if Path(r['path']).name.startswith('compile_compact_final')]
    need(len(controllers)==1 and controllers[0]['sha256']==CONTROLLERS[stage],'Wrong actual compact controller')
    bank=Path(assembly['original_Final_source']).parent.parent;base=load(bank/'PLAN.json')
    need(sha(bank/'PLAN.json')==p['original_plan_sha256'],'Protected old source-cold bank plan changed')
    oldrows={r['module']:r for r in base['sources']}
    excluded={f'W4D{stage}Final',f'W4D{stage}ClaimAudit'};expected_old=set(oldrows)-excluded
    inherited=p['inherited_closed_leaves'];need(len(inherited)==(118 if toy else 1031)and{r['module']for r in inherited}==expected_old,'Missing/extra numeric execution leaves')
    inherited_by_name={r['module']:r for r in inherited};need(len(inherited_by_name)==len(inherited),'Duplicate inherited leaf')
    for name,row in inherited_by_name.items():
        oldrow=oldrows[name];rp=bank/(name+'.COMPILED.json');strict=load(rp)
        route=base.get('routes',{}).get(name);logical=Path(route['logical_compile_origin'])if route else bank
        need(row['logical_compile_origin']==str(logical),'Changed old compiler origin')
        raw=old.receipt(bank,logical,oldrow,c['compiler'],True);need(raw==strict,'Ambiguous old receipt')
        need(row['source']==str(bank/'sources'/oldrow['file'])and row['source_sha256']==oldrow['sha256'],'Original numeric source differs')
        need(row['compiler_receipt']==str(rp)and row['receipt_sha256']==sha(rp)and row['object_sha256']==raw['object_sha256'],'Original accepted receipt/object differs')
        obj=run/'objects'/(name.replace('.','/')+'.olean');oldobj=Path(row['object'])
        need(oldobj==bank/'objects'/(name.replace('.','/')+'.olean')and sha(obj)==sha(oldobj)==raw['object_sha256'],'Actual inherited object differs')
        need(os.stat(obj).st_ino==os.stat(oldobj).st_ino and os.stat(obj).st_dev==os.stat(oldobj).st_dev,'Inherited numeric leaf not immutable hardlink')
    need(len(base['payloads'])==(91 if toy else 937),'Original literal input count differs')
    for row in base['payloads']:
        path=bank/'sources'/row['file'];need(path.stat().st_size==row['bytes']and sha(path)==row['sha256'],'Protected literal input differs')
    result_records={row['module']:row for row in result['records']}
    need(len(result_records)==5,'Duplicate/missing new compile result')
    actual_records={};all_root_axes=None
    for row in p['modules']:
        name=row['module'];source=assembly_dir/row['file'];need(sha(source)==row['sha256'],'Executed new source differs')
        raw=load(run/(name+'.COMPILED.json'));need(type(raw['returncode'])is int and raw['returncode']==0 and positive(raw['seconds']),'Actual compiler failed')
        cmd=['/usr/bin/time','-v','-o',str(run/(name+'.time')),'prlimit','--as=unlimited','--stack='+str(256*2**20),'--',c['compiler'],'-j1','--root='+str(assembly_dir),'-o',str(run/'objects'/(name+'.olean')),str(source)]
        need(raw['command']==cmd and raw['source_sha256']==row['sha256'],'New exact compiler/source/AS invocation differs')
        for ext in['stdout','stderr','time']:need(raw[ext+'_sha256']==sha(run/(name+'.'+ext)),'New compiler log/time changed')
        obj=run/'objects'/(name+'.olean');need(raw['object_sha256']==sha(obj),'Compiled new object changed')
        out=(run/(name+'.stdout')).read_text();err=(run/(name+'.stderr')).read_text();timing=(run/(name+'.time')).read_text()
        need(not err and not BAD.search(out),'Compiler diagnostic forbids acceptance')
        lint=re.findall(r'warning: ([^\n]*)',out);allowed_lint=['Unused tactic linter: `all_goals decide +kernel` does nothing','this tactic is never executed']if name==f'W4D{stage}Final'else[]
        need(not lint or lint==allowed_lint,'Unexpected compiler warning')
        rss=re.findall(r'Maximum resident set size \(kbytes\):\s*(\d+)',timing)
        need(len(rss)==1 and type(raw['peak_RSS_KiB'])is int and raw['peak_RSS_KiB']==int(rss[0])>0 and re.search(r'Exit status:\s*0\s*$',timing)and'Command terminated by signal'not in timing,'No actual completed GNUtime measurement')
        rp=result_records.get(name);need(rp is not None,'New compile missing from completed result')
        for k,v in raw.items():need(k in rp and rp[k]==v,'Result altered actual compiler receipt field '+k)
        marker=run/(name+'.markers')
        if raw['marker_sha256']is not None:need(marker.is_file()and raw['marker_path']==str(marker)and sha(marker)==raw['marker_sha256'],'Private phase marker differs')
        policy=raw['actual_child_policy']
        if policy is not None:need(policy['THP_enabled']==0 and policy['affinity']==[96,97,98,99]and re.search(r'^Max address space\s+unlimited\s+unlimited',policy['limits'],re.M),'Observed compiler resource policy differs')
        actual_axes=axes(out)
        if name==f'W4D{stage}ClaimAudit':
            typed_source=source.read_text();expected=[f'W4ClaimAudit{stage}.'+n for n in re.findall(r'^theorem (\w+)\b',typed_source,re.M)]
            need(sha(source)==fixed['original_audit']and len(expected)==stage+5,'Exact original typed source missing')
            all_root_axes=axes(out,expected);need(rp['actual_original_typed_root_axioms']==all_root_axes,'Recorded original root axioms differ')
        actual_records[name]=raw
    objectnames={str(x.relative_to(run/'objects').with_suffix('')).replace('/','.')for x in(run/'objects').rglob('*.olean')}
    need(objectnames==expected_old|set(actual_records),'Hidden/alternative application bank object')
    before=p['memory_events_before'];after=result['memory_events_after'];need(before['oom']==after['oom']==0 and before['oom_kill']==after['oom_kill']==0,'Actual owned OOM prevents acceptance')
    need(p['physical_limit_bytes']==result['physical_limit_bytes']==(64 if toy else 300)*2**30 and p['virtual_AS']=='unlimited','Declared physical/virtual scope differs')
    need(result['original_typed_roots']==stage+5 and result['inherited_source_associated_numerical_leaves']==len(inherited)and result['source_cold']is False and result['full_C_source_first_PV_claimed']is False and result['new_unverified_axioms_sorry_native']is False,'Verification tier/scope changed')
    need(result['max_individual_RSS_KiB']==max(r['peak_RSS_KiB']for r in actual_records.values())and positive(result['seconds']),'Compiler summary not actual')
    return dict(plan=p,result=result,assembly=assembly,base=base,bank=bank,oldrows=oldrows,inherited=inherited_by_name,new=actual_records,root_axioms=all_root_axes,compiler=c)


def verify_resources(a,state):
    need(all(x is not None and x.is_file()for x in[a.supervisor,a.command_plan,a.unit_policy,a.page_policy]),'Completed actual production resource evidence required')
    p=state['plan'];result=state['result'];s=load(a.supervisor);command=load(a.command_plan);unit=load(a.unit_policy);page=load(a.page_policy)
    need(s['status']=='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'and type(s['returncode'])is int and s['returncode']==0 and s['failure']is None and positive(s['seconds']),'Actual owned supervisor incomplete')
    expected=['/usr/bin/python3',str(Path(__file__).parent/'compile_compact_final_v2.py'),'--assembly',str(a.assembly),'--run',str(a.run),'--physical-gib','300']
    need(s['command']==command['command']==expected and s['command_file_sha256']==sha(a.command_plan),'Actual production argv differs')
    need(s['supervisor_sha256']==SUP_SHA==sha(S/'pv/supervise_resource_run.py'),'Unchanged outer supervisor differs')
    pins=command['source_pins'];need(len({r['path']for r in pins})==len(pins),'Duplicate production source pin')
    for row in pins:need(sha(Path(row['path']))==row['sha256'],'Pinned production source changed')
    need(any(Path(r['path']).name=='compile_compact_final_v2.py'and r['sha256']==CONTROLLERS[24]for r in pins),'Reviewed actual controller not pinned')
    need(unit['command_file_sha256']==sha(a.command_plan)and unit['supervisor_source_sha256']==SUP_SHA and unit['page_policy_source_sha256']==PAGE_SHA,'Owned unit policy lineage differs')
    properties=unit['command'];need(all('--property='+value in properties for value in['MemoryMax=300G','MemoryHigh=300G','MemorySwapMax=0','OOMPolicy=continue']),'Owned unit logging/physical policy differs')
    need(page['status']=='VERIFIED_PROCESS_PAGE_POLICY_BEFORE_EXEC_NOT_CHILD_OR_PROOF_ACCEPTANCE'and page['PR_GET_after']==1 and page['proc_THP_enabled']=='0'and page['actual_affinity']==[96,97,98,99]and page['wrapper_sha256']==PAGE_SHA==sha(S/'pv/generic_page_policy_exec.py'),'Actual inherited process page policy differs')
    expected_page_command=['/usr/bin/python3',str(S/'pv/supervise_resource_run.py'),'--root',str(D),'--command',str(a.command_plan),'--receipt',str(a.supervisor),'--live',str(D/'N24_COMPACT_LIVE_v2.json')]
    need(page['command']==expected_page_command,'Page policy belongs to another supervisor invocation')
    expected_unit=['systemd-run','--user','--unit','ivy-n24-compact-proof-v2','--property=MemoryMax=300G','--property=MemoryHigh=300G','--property=MemorySwapMax=0','--property=OOMPolicy=continue','--property=TasksMax=512','--property=LimitNOFILE=1048576','--property=TimeoutStopSec=90','--property=KillMode=control-group','/usr/bin/taskset','--cpu-list','96-99','/usr/bin/python3',str(S/'pv/generic_page_policy_exec.py'),'--disable-thp','--receipt',str(a.page_policy),'--',*expected_page_command]
    need(unit['command']==expected_unit,'Exact launch/resource/affinity invocation differs')
    admission=s['admission'];need(admission['available_RAM_bytes']>=2**40 and admission['free_disk_bytes']>=2**40 and admission['owned_scratch_bytes']<270*2**30,'Independent actual admission failed')
    for endpoint in[s['before'],s['final']]:
        need(endpoint['memory.max']==endpoint['memory.high']==str(300*2**30)and endpoint['memory.swap.max']=='0','Actual strict physical cap/noSwap differs')
        ev=parse_events(endpoint['memory.events']);need(ev['oom']==ev['oom_kill']==0,'Actual production OOM counter prevents acceptance')
    need(len(s['samples'])>0,'Missing actual independent supervisor samples')
    for row in s['samples']:
        need(row['available_RAM_bytes']>=256*2**30 and row['owned_scratch_bytes']<290*2**30,'Actual host/scratch reserve failed')
        cg=row['cgroup'];ev=parse_events(cg['memory.events'])
        need(cg['memory.max']==cg['memory.high']==str(300*2**30)and cg['memory.swap.max']=='0'and ev['oom']==ev['oom_kill']==0,'Actual sampled physical resource/OOM policy differs')
    out=a.supervisor.with_suffix('.stdout');err=a.supervisor.with_suffix('.stderr')
    need(s['stdout_sha256']==sha(out)and s['stderr_sha256']==sha(err)and not err.read_bytes(),'Actual supervisor output differs')
    need('PASS PRIVATE STAGED ORIGINAL CLAIMS 24'in out.read_text(),'No actual controller completion output')
    return dict(supervisor=str(a.supervisor),supervisor_sha256=sha(a.supervisor),command_plan=str(a.command_plan),command_plan_sha256=sha(a.command_plan),unit_policy=str(a.unit_policy),unit_policy_sha256=sha(a.unit_policy),page_policy=str(a.page_policy),page_policy_sha256=sha(a.page_policy),actual_final_memory_events=parse_events(s['final']['memory.events']),actual_aggregate_charge_peak_claimed=False,sampled_peak_cgroup_charge_bytes=max(int(v['cgroup']['memory.current'])for v in s['samples']),sampled_campaign_scratch_max_bytes=max(v['owned_scratch_bytes']for v in s['samples']),actual_supervisor_seconds=s['seconds'])


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['run','assembly','context','out']:ap.add_argument('--'+name,type=Path,required=True)
    for name in['supervisor','command-plan','unit-policy','page-policy']:ap.add_argument('--'+name,type=Path)
    ap.add_argument('--toy',action='store_true');a=ap.parse_args()
    for name in['run','assembly','context']:setattr(a,name,getattr(a,name).resolve(strict=True))
    need(not os.path.lexists(a.out),'Fresh independent acceptance receipt required')
    began=time.monotonic();state=verify_math(a.run,a.assembly,a.context,a.toy)
    resource=None if a.toy else verify_resources(a,state)
    stage=state['assembly']['stage'];count=len(state['inherited'])+4
    publish(a.out,dict(status='PASS_INDEPENDENT_COMPACT_NUMERICAL_KERNEL_ONLY_NOT_C_PV',toy_only=a.toy,stage=stage,N=2**stage,norm_numerator=13560177159173855 if a.toy else 7813568381279800,numerical_source_cold_leaves=len(state['inherited']),fresh_mathematical_proof_modules=4,math_bank_modules=count,actual_fresh_compiler_calls=5,import_probe_is_diagnostic_not_provider=True,typed_original_roots=stage+5,root_axioms=state['root_axioms'],all_original_numeric_sources_objects_and_literal_data_checked=True,original_outcomes_preserved=True,source_cold=False,source_first_PV_complete=False,plan_sha256=sha(a.run/'PLAN.json'),result_sha256=sha(a.run/'RESULT.json'),assembly_sha256=sha(a.assembly/'ASSEMBLY.json'),validator_sha256=sha(Path(__file__)),actual_resource_evidence=resource,seconds=time.monotonic()-began))
    print('PASS INDEPENDENT COMPACT NUMERICAL PROOF',stage,flush=True)
if __name__=='__main__':main()
