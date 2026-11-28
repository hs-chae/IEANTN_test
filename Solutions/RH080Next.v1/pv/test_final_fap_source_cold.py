#!/usr/bin/env python3
"""Actual all-mode CLI tests after completion; copied metadata fixtures only."""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
FILES={'supervisor':'FINAL_FAP_FULL_MAIN_SOURCE_COLD_SUPERVISOR.json','execution-plan':'FINAL_FAP_FULL_MAIN_SOURCE_COLD_EXECUTION_PLAN.json','driver-stdout':'final-fap-full-main-source-cold.stdout','driver-stderr':'final-fap-full-main-source-cold.stderr'}
def need(ok,msg):
    if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def write(p,data):
    if p.is_symlink():p.unlink()
    p.write_bytes(data)
def put(p,d):write(p,(json.dumps(d,indent=2)+'\n').encode())
def clone(source,evidence,dest):
    dest.mkdir();b=dest/'artifacts';b.mkdir();(b/'objects').symlink_to(source/'objects',target_is_directory=True);(b/'source').mkdir();(b/'logs').mkdir()
    for x in(source/'source').rglob('*.lean'):
        target=b/'source'/x.relative_to(source/'source');target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(x)
    for x in(source/'logs').iterdir():(b/'logs'/x.name).symlink_to(x)
    for x in source.glob('*.json'):shutil.copyfile(x,b/x.name)
    for key,name in FILES.items():
        if name.endswith('.json'):shutil.copyfile(evidence/name,dest/name)
        else:(dest/name).symlink_to(evidence/name)
    return b

def args(run,evidence,output):
    values=['--run',str(run)]
    for key,name in FILES.items():values+=['--'+key,str(evidence/name)]
    return values+['--output',str(output)]

def module_change(fixture,module,change):
    b=fixture/'artifacts';receipt=b/(module+'.COMPILED.json');q=load(receipt);change(b,q);put(receipt,q)
    attempt={k:v for k,v in q.items()if k!='object_sha256'};put(b/(module+'.ATTEMPT.json'),attempt)
    r=load(b/'RESULT.json');r['commands']=[q if x['module']==module else x for x in r['commands']];put(b/'RESULT.json',r)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',required=True,type=Path);ap.add_argument('--evidence-root',required=True,type=Path);ap.add_argument('--controls',required=True,type=Path);a=ap.parse_args()
    need((a.run/'RESULT.json').is_file()and(a.evidence_root/FILES['supervisor']).is_file(),'actual cold completion required before controls')
    need(not a.controls.exists(),'fresh controls directory required');a.controls.mkdir();env=dict(os.environ,GIT_OPTIONAL_LOCKS='0',PYTHONDONTWRITEBYTECODE='1');records=[]
    def execute(key,flags,script,arguments,success,reason=None):
        cmd=[sys.executable,*flags,str(HERE/script),*arguments];r=subprocess.run(cmd,capture_output=True,timeout=240,env=env);(a.controls/(key+'.stdout')).write_bytes(r.stdout);(a.controls/(key+'.stderr')).write_bytes(r.stderr)
        need((r.returncode==0)==success,'wrong CLI outcome '+key)
        if reason is not None:need(reason.encode()in r.stderr,'wrong rejection reason '+key)
        records.append(dict(case=key,command=cmd,exitcode=r.returncode,intended_error=reason));return r
    for flags in [[],['-O'],['-OO']]:
        mode=flags[0][1:]if flags else'normal'
        execute('actual-base-'+mode,flags,'reproduce_final_fap_source_cold.py',['--verify-only',str(a.run)],True)
        execute('actual-independent-'+mode,flags,'verify_final_fap_source_cold.py',args(a.run,a.evidence_root,a.controls/('ACCEPTED_'+mode+'.json')),True)
    tests={
      'missing-final-result':'missing completed atomic RESULT',
      'missing-owned-supervisor':'missing completed owned supervisor',
      'source-cache-fallback':'not complete fresh source-only execution',
      'omitted-source':'omitted/extra/collapsed source identity',
      'duplicate-source':'omitted/extra/collapsed source identity',
      'missing-real-compiler':'FFTMainIOOutput.COMPILED.json',
      'compiler-flags':'actual compiler flags/source/cache context differs',
      'frozen-source-mutation':'Frozen source differs FFTMainIOOutput',
      'panic-exit0':'Strict compiler diagnostic FFTMainIOOutput',
      'missing-full-main-audit':'Missing actual full-main finite ANT dependency audit',
      'new-final-axiom':'new final ANT axiom',
      'actual-OOM-event':'actual owned OOM events occurred',
      'invented-child-OOM-zero':'child must not invent actual OOM counters',
      'unowned-cgroup':'wrong owned cgroup identity',
      'RSS-summary':'actual compiler RSS aggregate differs',
      'duplicate-json-key':'duplicate JSON key'}
    removed=[]
    for name,reason in tests.items():
        f=a.controls/name;b=clone(a.run,a.evidence_root,f)
        if name=='missing-final-result':(b/'RESULT.json').unlink()
        elif name=='missing-owned-supervisor':(f/FILES['supervisor']).unlink()
        elif name=='source-cache-fallback':r=load(b/'RESULT.json');r['application_object_fallback']=True;put(b/'RESULT.json',r)
        elif name in ['omitted-source','duplicate-source']:
            p=load(b/'PLAN.json')
            if name=='omitted-source':p['source_rows'].pop()
            else:p['source_rows'][-1]=p['source_rows'][0]
            put(b/'PLAN.json',p)
        elif name=='missing-real-compiler':(b/'FFTMainIOOutput.COMPILED.json').unlink()
        elif name=='compiler-flags':module_change(f,'FFTMainIOOutput',lambda b,q:q['command'].append('--trust=1'))
        elif name=='frozen-source-mutation':p=b/'source/FFTMainIOOutput.lean';write(p,p.read_bytes()+b'\n')
        elif name=='panic-exit0':
            def panic(b,q):p=b/'logs/FFTMainIOOutput.stdout';write(p,b'PANIC injected despite exit0\n');q['stdout_sha256']=sha(p)
            module_change(f,'FFTMainIOOutput',panic)
        elif name in ['missing-full-main-audit','new-final-axiom']:
            def audit(b,q):
                p=b/'logs/FFTFapMainAudit.stdout';data=b''if name=='missing-full-main-audit'else p.read_bytes().replace(b'Classical.choice',b'NewTrust.axiom',1);write(p,data);q['stdout_sha256']=sha(p)
            module_change(f,'FFTFapMainAudit',audit)
        elif name=='actual-OOM-event':
            p=f/FILES['supervisor'];s=load(p);lines=s['final']['memory.events'].splitlines();s['final']['memory.events']='\n'.join('oom '+str(int(x.split()[1])+1)if x.split()[0]=='oom'else x for x in lines);put(p,s)
        elif name=='invented-child-OOM-zero':r=load(b/'RESULT.json');r['OOM_events']=0;put(b/'RESULT.json',r)
        elif name=='unowned-cgroup':p=f/FILES['supervisor'];s=load(p);s['final']['path']='/';put(p,s)
        elif name=='RSS-summary':r=load(b/'RESULT.json');r['peak_compiler_child_RSS_bytes']+=1;put(b/'RESULT.json',r)
        else:write(b/'RESULT.json',b'{"status":"PASS","status":"FAIL"}')
        for flags in [[],['-O'],['-OO']]:
            mode=flags[0][1:]if flags else'normal';output=a.controls/(name+'-'+mode+'.json')
            execute(name+'-'+mode,flags,'verify_final_fap_source_cold.py',args(b,f,output),False,reason);need(not output.exists(),'rejected completion wrote an acceptance')
            if name in ['missing-real-compiler','frozen-source-mutation','panic-exit0','missing-full-main-audit']:
                execute('base-'+name+'-'+mode,flags,'reproduce_final_fap_source_cold.py',['--verify-only',str(b)],False)
            if name=='missing-final-result':
                execute('base-artifact-only-no-final-'+mode,flags,'reproduce_final_fap_source_cold.py',['--verify-only',str(b)],True)
        # All fixtures are synthetic copies of metadata, not new cold proof results.
        need(f.parent==a.controls and not f.is_symlink(),'fixture cleanup ownership');removed.append(str(f));shutil.rmtree(f);need(not f.exists(),'fixture cleanup failed')
    # Same actual681-source run still validates after every isolated mutation.
    execute('actual-final-recheck',[],'verify_final_fap_source_cold.py',args(a.run,a.evidence_root,a.controls/'ACCEPTED_FINAL.json'),True)
    hashes={sha(a.controls/x)for x in ['ACCEPTED_normal.json','ACCEPTED_O.json','ACCEPTED_OO.json','ACCEPTED_FINAL.json']};need(len(hashes)==1,'positive acceptance differs across Python optimization')
    record=dict(status='PASS_FINAL_681_SOURCE_COLD_ALL_MODE_POSITIVES_AND_ISOLATED_MUTATIONS',base_positive_modes=3,independent_positive_modes=3,independent_negative_cases=len(tests),independent_negative_rejections=len(tests)*3,base_negative_rejections=12,base_artifact_recheck_without_RESULT_not_completion_claim=3,actual_source_modules=681,cases=records,positive_receipt_sha256=next(iter(hashes)),validator_sha256=sha(HERE/'verify_final_fap_source_cold.py'),harness_sha256=sha(Path(__file__)),regenerable_fixtures_removed=removed,actual_cold_sources_receipts_objects_supervisor_unchanged=True,source_controller_inputs_unmodified=True)
    put(a.controls/'RESULT.json',record);print(json.dumps({k:record[k]for k in ['status','independent_negative_cases','independent_negative_rejections','base_negative_rejections','positive_receipt_sha256']}))
if __name__=='__main__':main()
