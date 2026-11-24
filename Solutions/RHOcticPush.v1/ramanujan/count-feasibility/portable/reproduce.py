#!/usr/bin/env python3
"""Clean-machine count reproduction, reusing the existing source replay engine.

Only pinned generic libraries may be reused. Numerical proposals are regenerated
and every application proof is compiled. This conservative clean route uses at
most300GiB of summed virtual caps; it is slower than the separately recorded
physical-RAM-aware recovery using994 validated historical modules.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, re, shutil, subprocess, sys

HERE=Path(__file__).resolve().parent
PARENT=HERE.parent

def need(ok,message):
    if not ok:raise ValueError(message)

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for block in iter(lambda:f.read(8<<20),b''):h.update(block)
    return h.hexdigest()

def read(path):
    def pairs(items):
        d={}
        for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(Path(path).read_text(),object_pairs_hook=pairs,
        parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))

def save(path,data):
    p=Path(path);q=p.with_suffix('.pending');q.write_text(json.dumps(data,indent=2)+'\n');os.replace(q,p)

def modulepath(name):return Path(*name.split('.')).with_suffix('.lean')

def frozen():
    m=read(HERE/'SOURCE_CLOSURE.json')
    for row in m['modules']:need(sha(HERE/'source'/row['relative'])==row['source_sha256'],'frozen application source')
    for row in m['resources']:need(sha(HERE/'source'/row['relative'])==row['sha256'],'frozen actual C source')
    c=read(HERE/'CONTROLLERS.json')
    for row in c['controllers']:need(sha(HERE/row['path'])==row['sha256'],'unchanged existing replay engine')
    g=read(PARENT/'REGENERATION.json')
    need(sha(PARENT/'regeneration/generate_demand_certificate_resources.py')==g['generator_sha256'],'original generator source')
    need(sha(PARENT/'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json')==g['identity_lock_sha256'],'original all3464source identity lock')
    return m,g

def isolated_engine(out):
    p=out/'engine/Solutions/Replay/scripts'
    for row in read(HERE/'CONTROLLERS.json')['controllers']:
        need(sha(p/Path(row['path']).name)==row['sha256'],'isolated replay engine identity')
    return p/'reproduce_profiled_closure.py'

def import_recovery():
    p=PARENT/'recover_count.py';s=importlib.util.spec_from_file_location('frozen_recovery_generator',p)
    m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
    need(m.sha(p)=='a58fe8105587ea9b94beace2d5c6ab29b3225e9b9bea023d65e0cf78f29b61b1',
        'same reviewed pure-leaf generator')
    return m

def run_command(out,name,cmd):
    with (out/(name+'.stdout')).open('w')as fo,(out/(name+'.stderr')).open('w')as fe:
        cp=subprocess.run(['/usr/bin/time','-v','-o',str(out/(name+'.resources.txt')),*cmd],stdout=fo,stderr=fe)
    need(cp.returncode==0,'stage failed:'+name)
    return dict(name=name,command=cmd,returncode=cp.returncode,
        **{f+'_sha256':sha(out/(name+'.'+f))for f in ['stdout','stderr','resources.txt']})

def checked_numeric(out,namespace,count):
    result=read(out/'replay/RESULT.json');rows={r['module']:r for r in result['records']}
    need(len(rows)==len(result['records']),'unique compiler identities')
    for row in result['records']:
        need(type(row['exit_code'])is int and row['exit_code']==0,'strict actual compiler success')
        need(row['source_unchanged_during_compile']is True,'actual unchanged compilation source')
    for i in range(count):
        mod=namespace+'.Check'+format(i,'04d');symbol=namespace+'.part_'+format(i,'04d')
        text=Path(rows[mod]['stdout']).read_text()
        need("'"+symbol+"' does not depend on any axioms"in text,'actual empty-axiom numerical fact')
        need(not re.search(r"'"+re.escape(symbol)+r"' depends on axioms:",text),'nonempty numerical fact')
    text=Path(rows[namespace+'.GapCheck']['stdout']).read_text()
    need("'"+namespace+".gaps_checked' does not depend on any axioms"in text,'empty-axiom prime gaps')
    return result

def validate(out,candidate=None):
    m,g=frozen();r=read(candidate or out/'RESULT.json');need(r['status']in ['PASS_FULL_CLEAN_COUNT_AND_SOURCE_MODEL','PASS_SMALL_WORKFLOW_CONTROL'],
        'complete clean reproduction required')
    need(r['wrapper_sha256']==sha(out/'reproduce.executed.py'),'actual executed wrapper identity')
    need(r['wrapper_sha256']in {sha(__file__),
        'e21ec439ee69c8bca6496df188dd633f3408320f1f9a600955e808ce33f0b2a4'},
        'current or explicitly retained completed workflow controller')
    need(r['source_manifest_sha256']==sha(out/'SOURCES.json'),'exact clean source manifest')
    sources=read(out/'SOURCES.json')['modules']
    need(type(r['smoke'])is bool,'strict workflow type')
    namespace='RamanujanPV.PureCountWorkflowControl'if r['smoke']else'RamanujanPV.HighTransitionCount'
    target=[1000,168]if r['smoke']else[1490000000000,55206486339]
    need(r['namespace']==namespace and r['exact_count']==target,'exact typed scientific target')
    proposal=read(out/'proposal/PROPOSAL.json');recovery=import_recovery()
    need(sha(out/'proposal/PROPOSAL.json')==read(out/'SOURCES.json')['untrusted_proposal_sha256'],'regenerated proposal identity')
    if not r['smoke']:
        lock=read(PARENT/'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json')
        need(proposal['packed_sha256']==g['original_packed_sha256']and
            {q['module']:q['sha256']for q in proposal['modules']}==lock['modules'],
            'fixed original full numerical source population')
    chunks=(proposal['records']+32767)//32768
    need(type(r['arithmetic_chunks'])is int and r['arithmetic_chunks']==chunks,
        'complete arithmetic population')
    expected={q['module']:q['sha256']for q in proposal['modules']}
    expected.update({q['module']:q['source_sha256']for q in m['modules']})
    for i in range(chunks):
        text=recovery.leaf_text(format(i,'04d'),i*32768,min(32768,proposal['records']-i*32768))
        if r['smoke']:text=text.replace('HighTransitionCount','PureCountWorkflowControl')
        expected[namespace+'.Check'+format(i,'04d')]=hashlib.sha256(text.encode()).hexdigest()
    consumer=recovery.closed_consumer()
    if r['smoke']:consumer=consumer.replace('HighTransitionCount','PureCountWorkflowControl').replace('1490000000000','1000').replace('55206486339','168')
    expected['RecoveredCountConsumer']=hashlib.sha256(consumer.encode()).hexdigest()
    need({q['module']:q['source_sha256']for q in sources}==expected and len(sources)==len(expected),
        'independent canonical source/statement recipes, no dropped or added source')
    for q in sources:
        need(sha(out/'source'/modulepath(q['module']))==q['source_sha256'],'clean source drift')
    for q in m['resources']:need(sha(out/'source'/q['relative'])==q['sha256'],'clean included C bytes')
    cmd=[sys.executable,str(isolated_engine(out)),'--check',str(out/'replay')]
    cp=subprocess.run(cmd,capture_output=True,text=True);need(cp.returncode==0,'independent existing replay readback:'+cp.stderr[-1000:])
    symbols=[namespace+'.part_'+format(i,'04d')for i in range(chunks)]
    symbols +=[namespace+'.gaps_checked',namespace+'.entries_checked',namespace+'.root_'+str(target[0]),namespace+'.pi_'+str(target[0])]
    symbols +=['RHOcticPush.RecoveredCount.'+n for n in ['count','actual_C_model_execution','exact_source_bytes_and_execution']]
    need(read(out/'replay/PLAN.json')['selected_theorems']==symbols,'all numerical and exact final consumer axiom audits')
    checked_numeric(out,r['namespace'],r['arithmetic_chunks'])
    need(r['old_application_objects_used']is False and r['new_source_first_PV_claim']is False,'trust labels')
    if not r['smoke']:need(r['exact_count']==[1490000000000,55206486339]and r['arithmetic_chunks']==2768,'locked full scientific result')
    return r

def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path);p.add_argument('--out',type=Path)
    p.add_argument('--check',type=Path);p.add_argument('--cpus',default='0,1,2,3');p.add_argument('--jobs',type=int,default=4)
    p.add_argument('--smoke',action='store_true');p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    if a.check:
        need(a.out is None and a.context is None and not a.prepare_only and not a.smoke,'readback route arguments')
        r=validate(a.check.resolve());print(r['status']);return
    need(a.out is not None and a.context is not None,'--out and portable pinned --context required')
    need(1<=a.jobs<=32,'bounded jobs');cpus=list(map(int,a.cpus.split(',')))
    need(len(cpus)==len(set(cpus))and len(cpus)>=a.jobs and set(cpus)<=os.sched_getaffinity(0),'available CPU affinity')
    m,g=frozen();recovery=import_recovery();out=a.out.resolve();need(not out.exists(),'fresh clean output')
    wrapper_before=sha(__file__);out.mkdir();(out/'reproduce.executed.py').write_bytes(Path(__file__).read_bytes())
    stages=[];query=1000 if a.smoke else 1490000000000
    engine=out/'engine/Solutions/Replay/scripts';engine.mkdir(parents=True)
    for row in read(HERE/'CONTROLLERS.json')['controllers']:
        (engine/Path(row['path']).name).write_bytes((HERE/row['path']).read_bytes())
    name='PureCountWorkflowControl'if a.smoke else'HighTransitionCount';namespace='RamanujanPV.'+name
    gen=PARENT/'regeneration/generate_demand_certificate_resources.py'
    stages.append(run_command(out,'regenerate',[sys.executable,str(gen),'--queries',str(query),'--name',name,
        '--out',str(out/'proposal'),'--cpus',','.join(map(str,cpus[:4])),'--memory-gib','128',
        '--data-chunk','131072','--proof-chunk','32768','--max-records','100000000']))
    proposal=read(out/'proposal/PROPOSAL.json')
    if not a.smoke:
        lock=read(PARENT/'regeneration/HIGH_ORIGINAL_REPRODUCTION_IDENTITIES.json')
        need(proposal['packed_sha256']==g['original_packed_sha256']and
            {q['module']:q['sha256']for q in proposal['modules']}==lock['modules'],
            'all regenerated original data/source identities')
    src=out/'source';shutil.copytree(out/'proposal/source',src)
    for q in m['modules']:
        f=src/q['relative'];f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes((HERE/'source'/q['relative']).read_bytes())
    for q in m['resources']:
        f=src/q['relative'];f.parent.mkdir(parents=True,exist_ok=True);f.write_bytes((HERE/'source'/q['relative']).read_bytes())
    chunks=(proposal['records']+32767)//32768
    for i in range(chunks):
        n=min(32768,proposal['records']-i*32768)
        text=recovery.leaf_text(format(i,'04d'),i*32768,n)
        if a.smoke:text=text.replace('HighTransitionCount',name)
        (src/modulepath(namespace+'.Check'+format(i,'04d'))).write_text(text)
    consumer=recovery.closed_consumer()
    value=proposal['results'][0]['value']
    if a.smoke:consumer=consumer.replace('HighTransitionCount',name).replace('1490000000000',str(query)).replace('55206486339',str(value))
    (src/'RecoveredCountConsumer.lean').write_text(consumer)
    rows=[]
    for f in sorted(src.rglob('*.lean')):rows.append(dict(module='.'.join(f.relative_to(src).with_suffix('').parts),source_sha256=sha(f)))
    save(out/'SOURCES.json',dict(modules=rows,untrusted_proposal_sha256=sha(out/'proposal/PROPOSAL.json')))
    profiles=dict(exact={namespace+'.Gaps':24,namespace+'.Data':128,namespace+'.GapCheck':192,
        namespace+'.Final':256,'RamanujanPV.SelectedReplayAudit':256},
        prefix={namespace+'.Data':9,namespace+'.Check':128})
    save(out/'PROFILES.json',profiles)
    symbols=[namespace+'.part_'+format(i,'04d')for i in range(chunks)]
    symbols +=[namespace+'.gaps_checked',namespace+'.entries_checked',namespace+'.root_'+str(query),namespace+'.pi_'+str(query)]
    symbols +=['RHOcticPush.RecoveredCount.'+n for n in ['count','actual_C_model_execution','exact_source_bytes_and_execution']]
    cmd=[sys.executable,str(isolated_engine(out)),'--context',str(a.context.resolve()),
        '--out',str(out/'replay'),'--application-source-root',str(src),'--root','RecoveredCountConsumer',
        '--jobs',str(a.jobs),'--cpus',a.cpus,'--memory-gib','128','--profile-json',str(out/'PROFILES.json'),
        '--aggregate-gib','300','--host-reserve-gib','512']
    for s in symbols:cmd+=['--theorem',s]
    if a.prepare_only:
        save(out/'PREPARED.json',dict(status='SOURCE_PREPARED_NO_PROOF_COMPILERS',command=cmd,
            generated_chunks=chunks,smoke=a.smoke));print('SOURCE_PREPARED_NO_PROOF_COMPILERS');return
    stages.append(run_command(out,'compile_all',cmd));checked_numeric(out,namespace,chunks)
    need(sha(__file__)==wrapper_before,'unchanged wrapper through clean reproduction')
    r=dict(status='PASS_SMALL_WORKFLOW_CONTROL'if a.smoke else'PASS_FULL_CLEAN_COUNT_AND_SOURCE_MODEL',
        wrapper_sha256=wrapper_before,source_manifest_sha256=sha(out/'SOURCES.json'),
        namespace=namespace,exact_count=[query,value],arithmetic_chunks=chunks,smoke=a.smoke,
        old_application_objects_used=False,new_source_first_PV_claim=False,stages=stages,
        trust='Kernel numerical certificates plus exact rendered C source/function model execution. Independent parser and physical CLI/stdout adequacy are not asserted.')
    save(out/'CANDIDATE.json',r);validate(out,out/'CANDIDATE.json')
    os.replace(out/'CANDIDATE.json',out/'RESULT.json')
    print(r['status'])
if __name__=='__main__':main()
