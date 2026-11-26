#!/usr/bin/env python3
"""Actual portable-proof completion CLI controls, preserving accepted source artifacts."""
import argparse,json,shutil,subprocess,sys
from pathlib import Path
import run_review as common
HERE=Path(__file__).resolve().parent


def clone(source,target):
    target.mkdir()
    for p in source.iterdir():
        if p.name in ['common','trials','logs']:
            (target/p.name).symlink_to(p.resolve(),target_is_directory=True)
        elif p.is_file():shutil.copyfile(p,target/p.name)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',required=True,type=Path);ap.add_argument('--out',required=True,type=Path);args=ap.parse_args()
    common.need((args.run/'RESULT.json').is_file(),'Actual completed source-cold result required')
    common.need(not args.out.exists(),'Fresh owned control directory required');args.out.mkdir(parents=True);rows=[]
    for opt in [0,1,2]:
        flags=[]if opt==0 else ['-O']if opt==1 else ['-OO']
        for case in ['positive','missing-final-result','application-cache','primary-promotion','missing-compiler-route','compiler-receipt-mismatch']:
            label=case+'-'+str(opt);run=args.run;fixture=None
            if case!='positive':
                fixture=args.out/(label+'-fixture');clone(args.run,fixture);run=fixture
                if case=='missing-final-result':(fixture/'RESULT.json').unlink()
                else:
                    result=common.load(fixture/'RESULT.json')
                    if case=='application-cache':result['original_application_object_fallback']=True
                    elif case=='primary-promotion':result['primary_successes_added']=13
                    elif case=='missing-compiler-route':result['commands'].pop()
                    else:result['commands'][0]['source_sha256']='0'*64
                    (fixture/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
            receipt=args.out/(label+'.json');command=[sys.executable,*flags,str(HERE/'check_clean_proofs.py'),'--run',str(run),'--output',str(receipt)]
            result=subprocess.run(command,capture_output=True,text=True)
            (args.out/(label+'.stdout')).write_text(result.stdout);(args.out/(label+'.stderr')).write_text(result.stderr)
            common.need(result.returncode==0 and receipt.is_file() if case=='positive' else result.returncode!=0 and not receipt.exists(),'Wrong actual portable completion CLI outcome '+label)
            rows.append(dict(case=case,optimization=opt,command=command,returncode=result.returncode,stdout_sha256=common.sha(args.out/(label+'.stdout')),stderr_sha256=common.sha(args.out/(label+'.stderr'))))
            if fixture:
                common.need(fixture.parent==args.out and not fixture.is_symlink(),'Cleanup escaped owned fixture');shutil.rmtree(fixture)
    common.save(args.out/'RESULT.json',dict(status='PASS_PORTABLE_SOURCE_COLD_ACTUAL_COMPLETION_CLIS_NORMAL_O_OO',positive=3,rejections=15,
        rows=rows,validator_sha256=common.sha(HERE/'check_clean_proofs.py'),controller_sha256=common.sha(Path(__file__)),
        original_evidence_modified=False,owned_metadata_fixtures_cleaned=True))
    print('PASS actual3positive+15negative portable completion CLI controls')


if __name__=='__main__':main()
