#!/usr/bin/env python3
"""Actual read-only completion-gate tests on a completed13-stage lineage fixture."""
import argparse,json,os,shutil,subprocess,sys
from pathlib import Path
from reproduce_dual import need,load,sha,publish
HERE=Path(__file__).resolve().parent


def clone(source,target):
    target.mkdir()
    for p in source.iterdir():
        if p.is_dir():
            for q in p.rglob('*'):
                if q.is_file():
                    t=target/q.relative_to(source);t.parent.mkdir(parents=True,exist_ok=True);os.link(q,t)
        elif p.suffix=='.json':shutil.copyfile(p,target/p.name)
        elif p.is_file():os.link(p,target/p.name)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['run','context','candidate','out']:ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh read-only verifier controls required');a.out.mkdir(parents=True)
    r=load(a.run/'RESULT.json');need(r['stages']==13,'Only bounded real13-stage mathematical fixtures allowed');records=[]
    for mode,flags in [(0,[]),(1,['-O']),(2,['-OO'])]:
        for case in['positive','missing-result','monolithic-label','wrong-count','compiler-flags','axiom-audit','RSS-summary']:
            fixture=None;run=a.run
            if case!='positive':
                fixture=a.out/(case+'-'+str(mode)+'-fixture');clone(a.run,fixture);run=fixture
                if case=='missing-result':(fixture/'RESULT.json').unlink()
                elif case=='axiom-audit':
                    p=fixture/'AXIOM_AUDIT.json';v=load(p);v['roots'][0]['axioms'].append('NewUnverifiedAxiom');p.write_text(json.dumps(v,indent=2)+'\n')
                elif case=='compiler-flags':
                    p=fixture/'W4D13ClaimAudit.COMPILED.json';v=load(p);v['command'].append('--trust=1');p.write_text(json.dumps(v,indent=2)+'\n')
                else:
                    p=fixture/'RESULT.json';v=load(p)
                    if case=='monolithic-label':v['source_cold']=True
                    elif case=='wrong-count':v['freshly_compiled_modules']+=1
                    else:v['max_individual_RSS_KiB']+=1
                    p.write_text(json.dumps(v,indent=2)+'\n')
            receipt=a.out/(case+'-'+str(mode)+'.json');command=[sys.executable,*flags,str(HERE/'verify_fft_dag_lineage_resume.py'),'--run',str(run),'--context',str(a.context),'--candidate',str(a.candidate),'--proof-only-toy','--output',str(receipt)]
            p=subprocess.run(command,capture_output=True,text=True);(a.out/(case+'-'+str(mode)+'.stdout')).write_text(p.stdout);(a.out/(case+'-'+str(mode)+'.stderr')).write_text(p.stderr)
            need(p.returncode==0 and receipt.is_file()if case=='positive'else p.returncode!=0 and not receipt.exists(),'Actual completion gate wrong result '+case+'/'+str(mode))
            records.append(dict(case=case,optimization=mode,command=command,returncode=p.returncode))
            if fixture:
                need(fixture.parent==a.out and not fixture.is_symlink(),'Owned metadata cleanup escaped');shutil.rmtree(fixture)
    publish(a.out/'RESULT.json',dict(status='PASS_ACTUAL_LINEAGE_COMPLETION_GATE_NORMAL_O_OO_AND18_NEGATIVE_REJECTIONS',positives=3,rejections=18,records=records,
        validator_sha256=sha(HERE/'verify_fft_dag_lineage_resume.py'),harness_sha256=sha(Path(__file__)),mathematical_proof_objects_and_original_sources_unchanged=True,
        production_N24_resource_gate_not_yet_run=True))
    print('PASS actual3positive+18negative completion-gate CLIs on real13-stage proof lineage')


if __name__=='__main__':main()
