#!/usr/bin/env python3
"""Actual small nested-lineage compiler and tamper controls; no N24 launch."""
import argparse,json,os,shutil,subprocess,sys
from pathlib import Path
from reproduce_dual import need,load,sha,publish
from test_fft_dag_resume_bounded import fixture,local_write
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['context','candidate','original-prefix','continuation','out']:ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh nested control directory required');a.out.mkdir(parents=True)
    original_plan=load(a.original_prefix/'PLAN.json');need(original_plan['proposal']['stages']==13,'Bounded13-stage fixture required')
    partial=a.out/'interrupted-continuation-fixture';fixture(a.continuation,partial,{'W4D13ClaimAudit'});os.link(a.continuation/'resume_driver.executed.py',partial/'resume_driver.executed.py')
    records=[]
    for opt in[0,1,2]:
        flags=[]if opt==0 else ['-O']if opt==1 else ['-OO'];out=a.out/('positive-'+str(opt))
        command=[sys.executable,*flags,str(HERE/'resume_fft_dag_source_cold_v2.py'),'--context',str(a.context),'--candidate',str(a.candidate),'--prefix',str(a.original_prefix),'--continuation',str(partial),'--run',str(out),'--workers','1','--worker-memory-gib','64']
        p=subprocess.run(command,capture_output=True,text=True);(a.out/('positive-'+str(opt)+'.stdout')).write_text(p.stdout);(a.out/('positive-'+str(opt)+'.stderr')).write_text(p.stderr)
        need(p.returncode==0 and(out/'RESULT.json').is_file(),'Actual nested toy compiler failed '+str(opt));r=load(out/'RESULT.json')
        need(r['reused_original_source_cold_modules']==118 and r['reused_prior_continuation_modules']==1 and r['freshly_compiled_modules']==1 and r['modules']==120,'Nested origin counts differ')
        need(r['audited_roots']==18 and r['source_cold']is False,'Nested typed proof or freshness misclassified')
        need(load(out/'W4D13ClaimAudit.COMPILED.json')['command'][3]==str(out/'sources'),'Unreceipted object reused instead of actual new compiler')
        records.append(dict(case='118original+1continuation+1fresh',optimization=opt,command=command,returncode=p.returncode,result_sha256=sha(out/'RESULT.json')))
    for case in['new-object-mismatch','new-command-flag','new-panic-exit0','changed-parent-plan','altered-original-receipt','missing-original-dependency','unknown-new-receipt']:
        broken=a.out/(case+'-fixture');fixture(a.continuation,broken,{'W4D13ClaimAudit'});os.link(a.continuation/'resume_driver.executed.py',broken/'resume_driver.executed.py');p=broken/'W4D13Final.COMPILED.json';r=load(p)
        if case=='new-object-mismatch':local_write(broken/'objects/W4D13Final.olean',b'unverified object')
        elif case=='new-command-flag':r['command'].append('--trust=1');p.write_text(json.dumps(r,indent=2)+'\n')
        elif case=='new-panic-exit0':
            local_write(broken/'W4D13Final.stderr',b'PANIC despite exit0\n');r['stderr_sha256']=sha(broken/'W4D13Final.stderr');p.write_text(json.dumps(r,indent=2)+'\n')
        elif case=='changed-parent-plan':p=broken/'PLAN.json';r=load(p);r['original_plan_sha256']='0'*64;p.write_text(json.dumps(r,indent=2)+'\n')
        elif case=='altered-original-receipt':p=broken/'FapData.COMPILED.json';r=load(p);r['source_sha256']='0'*64;p.write_text(json.dumps(r,indent=2)+'\n')
        elif case=='missing-original-dependency':(broken/'FapData.COMPILED.json').unlink()
        else:(broken/'Alien.COMPILED.json').write_text('{}\n')
        for opt in[0,1,2]:
            flags=[]if opt==0 else ['-O']if opt==1 else ['-OO'];out=a.out/(case+'-rejected-'+str(opt));command=[sys.executable,*flags,str(HERE/'resume_fft_dag_source_cold_v2.py'),'--context',str(a.context),'--candidate',str(a.candidate),'--prefix',str(a.original_prefix),'--continuation',str(broken),'--run',str(out),'--workers','1','--prepare-only']
            v=subprocess.run(command,capture_output=True,text=True);(a.out/(case+'-'+str(opt)+'.stdout')).write_text(v.stdout);(a.out/(case+'-'+str(opt)+'.stderr')).write_text(v.stderr)
            need(v.returncode!=0 and not out.exists(),'Corrupt nested prefix admitted '+case);records.append(dict(case=case,optimization=opt,command=command,returncode=v.returncode))
        need(broken.parent==a.out and not broken.is_symlink(),'Owned nested fixture cleanup escaped');shutil.rmtree(broken)
    publish(a.out/'RESULT.json',dict(status='PASS_REAL_SMALL_NESTED_LINEAGE_NORMAL_O_OO_AND21_TAMPER_REJECTIONS',positive_modes=3,negative_rejections=21,records=records,
        controller_sha256=sha(HERE/'resume_fft_dag_source_cold_v2.py'),helper_sha256=sha(HERE/'fft_dag_nested_lineage.py'),harness_sha256=sha(Path(__file__)),
        original_cold_and_first_continuation_unchanged=True,n24_large_continuation_not_launched=True))
    print('PASS actual3nested118+1+1 compiler runs and21negative lineage CLIs')


if __name__=='__main__':main()
