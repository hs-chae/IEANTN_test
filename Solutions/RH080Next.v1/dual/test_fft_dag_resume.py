#!/usr/bin/env python3
"""Bounded actual-CLI resume tests on an existing small genuine cold DAG.

Fixtures are explicitly synthetic partial snapshots of a completed small run.
They preserve all original records and never change the N24 candidate/outcomes.
"""
import argparse,json,os,shutil,subprocess,sys
from pathlib import Path
from reproduce_dual import need,sha,load,publish
HERE=Path(__file__).resolve().parent


def hardlink(source,target):
    target.parent.mkdir(parents=True,exist_ok=True);os.link(source,target)


def fixture(source,target,excluded):
    target.mkdir();shutil.copyfile(source/'PLAN.json',target/'PLAN.json')
    for name in ['driver.executed.py','producer.executed.py']:hardlink(source/name,target/name)
    for root in ['sources','objects']:
        (target/root).mkdir()
        for path in(source/root).rglob('*'):
            if path.is_file():hardlink(path,target/root/path.relative_to(source/root))
    for path in source.glob('*.COMPILED.json'):
        module=path.name.removesuffix('.COMPILED.json')
        if module not in excluded:
            shutil.copyfile(path,target/path.name)
            for ext in ['stdout','stderr','time']:hardlink(source/(module+'.'+ext),target/(module+'.'+ext))


def local_write(path,data):
    path.unlink();path.write_bytes(data)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context','candidate','cold','out']:ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh toy control directory required');a.out.mkdir(parents=True)
    original=load(a.cold/'PLAN.json');stages=original['proposal']['stages'];need(stages==13,'Only bounded13-stage fixtures allowed')
    excluded={original['proposal']['final_module'],f'W4D{stages}ClaimAudit'}
    base=a.out/'partial-fixture';fixture(a.cold,base,excluded);records=[]
    successful=len(original['sources'])-len(excluded)
    for opt in [0,1,2]:
        flags=[]if opt==0 else ['-O']if opt==1 else ['-OO'];out=a.out/('actual-resume-'+str(opt))
        command=[sys.executable,*flags,str(HERE/'resume_fft_dag_source_cold.py'),'--context',str(a.context),'--candidate',str(a.candidate),'--prefix',str(base),'--run',str(out),'--workers','1','--worker-memory-gib','64']
        p=subprocess.run(command,capture_output=True,text=True);(a.out/('positive-'+str(opt)+'.stdout')).write_text(p.stdout);(a.out/('positive-'+str(opt)+'.stderr')).write_text(p.stderr)
        need(p.returncode==0 and(out/'RESULT.json').is_file(),'Actual toy resume failed '+str(opt))
        result=load(out/'RESULT.json');need(result['reused_successful_source_cold_modules']==successful and result['freshly_compiled_modules']==2 and result['modules']==len(original['sources']),'Wrong actual reuse/fresh counts')
        need(result['source_cold']is False and result['source_cold_lineage_resume']is True,'Resume mislabeled monolithic fresh')
        for name in excluded:need(load(out/(name+'.COMPILED.json'))['command'][3]==str(out/'sources'),'Fresh compiler used wrong source root')
        for name in set(r['module']for r in original['sources'])-excluded:
            old=a.cold/'objects'/(name.replace('.','/')+'.olean');new=out/'objects'/(name.replace('.','/')+'.olean')
            need(os.stat(old).st_ino==os.stat(new).st_ino and os.stat(old).st_dev==os.stat(new).st_dev,'Reused object was copied')
        for item in original['payloads']:
            old=a.candidate/item['file'];new=out/'sources'/item['file'];need(os.stat(old).st_ino==os.stat(new).st_ino,'Literal data was copied')
        records.append(dict(case='actual2fresh-compilers',optimization=opt,command=command,returncode=p.returncode,reused=successful,fresh=2,result_sha256=sha(out/'RESULT.json')))
    cases=['object-mismatch','panic-exit0','time-RSS-mismatch','compiler-flag','missing-dependency','wrong-fixed-claim','unknown-receipt','missing-literal']
    for case in cases:
        broken=a.out/(case+'-fixture');fixture(a.cold,broken,excluded);name='FapData';p=broken/(name+'.COMPILED.json');record=load(p)
        if case=='object-mismatch':local_write(broken/'objects/FapData.olean',b'not an accepted proof object')
        elif case=='panic-exit0':
            local_write(broken/'FapData.stderr',b'PANIC despite exit0\n');record['stderr_sha256']=sha(broken/'FapData.stderr');p.write_text(json.dumps(record,indent=2)+'\n')
        elif case=='time-RSS-mismatch':record['peak_RSS_KiB']+=1;p.write_text(json.dumps(record,indent=2)+'\n')
        elif case=='compiler-flag':record['command'].append('--trust=1');p.write_text(json.dumps(record,indent=2)+'\n')
        elif case=='missing-dependency':p.unlink()
        elif case=='wrong-fixed-claim':
            plan=load(broken/'PLAN.json');row=next(r for r in plan['sources']if r['module']==f'W4D{stages}ClaimAudit');source=broken/'sources'/row['file'];local_write(source,source.read_bytes().replace(b'theorem numerator :',b'theorem different_claim :'));row['sha256']=sha(source);(broken/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
        elif case=='unknown-receipt':(broken/'Alien.COMPILED.json').write_text('{}\n')
        else:(broken/'sources'/original['payloads'][0]['file']).unlink()
        for opt in [0,1,2]:
            flags=[]if opt==0 else ['-O']if opt==1 else ['-OO'];out=a.out/(case+'-rejected-'+str(opt));command=[sys.executable,*flags,str(HERE/'resume_fft_dag_source_cold.py'),'--context',str(a.context),'--candidate',str(a.candidate),'--prefix',str(broken),'--run',str(out),'--workers','1','--prepare-only']
            result=subprocess.run(command,capture_output=True,text=True);(a.out/(case+'-'+str(opt)+'.stdout')).write_text(result.stdout);(a.out/(case+'-'+str(opt)+'.stderr')).write_text(result.stderr)
            need(result.returncode!=0 and not out.exists(),'Invalid prefix admitted '+case+'/'+str(opt));records.append(dict(case=case,optimization=opt,command=command,returncode=result.returncode))
        need(broken.parent==a.out and not broken.is_symlink(),'Owned fixture cleanup escaped');shutil.rmtree(broken)
    publish(a.out/'RESULT.json',dict(status='PASS_ACTUAL_SMALL_SOURCE_COLD_LINEAGE_RESUME_NORMAL_O_OO_AND24_NEGATIVE_REJECTIONS',
        positive_modes=3,reused_modules_each=successful,fresh_modules_each=2,negative_cases=8,negative_rejections=24,
        records=records,controller_sha256=sha(HERE/'resume_fft_dag_source_cold.py'),harness_sha256=sha(Path(__file__)),original_candidate_and_cold_run_unchanged=True,
        actual_N24_continuation_launched=False,synthetic_partial_fixture_explicit=True))
    print('PASS actual3smallresumes/6freshcompilers and24negative prefix-rejection CLIs')


if __name__=='__main__':main()
