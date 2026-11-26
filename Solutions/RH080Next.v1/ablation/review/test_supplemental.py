#!/usr/bin/env python3
"""Actual CLI rejection controls, using isolated copies of accepted review files."""
import argparse,json,shutil,subprocess,sys
from pathlib import Path
import run_review as common
HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--runs',required=True,type=Path);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args();common.need(not a.out.exists(),'Fresh controls path required');a.out.mkdir(parents=True)
    original=common.load(a.runs);target=next(r for r in original['rows'] if r['trial']=='fixed_width-C_network-r1');base=Path(target['out']);checks=[]
    for opt in [0,1,2]:
        flags=[] if opt==0 else ['-O'] if opt==1 else ['-OO']
        for kind in ['positive','runtime-mismatch','missing-second-source','nonstandard-axiom','primary-reclassification']:
            label=kind+'-'+str(opt);runs=a.runs;fixture=None
            if kind!='positive':
                fixture=a.out/(label+'-fixture');fixture.mkdir();run=fixture/'trial';run.mkdir();shutil.copytree(base/'submission',run/'submission');shutil.copy2(base/'result.json',run/'result.json');shutil.copy2(base.with_name(base.name+'.INPUTS.json'),fixture/'trial.INPUTS.json')
                review=common.load(run/'submission/REVIEW.json')
                if kind=='runtime-mismatch':
                    p=fixture/'trial.INPUTS.json';v=common.load(p);v['common_runtime_sha256']='0'*64;p.write_text(json.dumps(v,indent=2)+'\n')
                elif kind=='missing-second-source':review['source_modules']=review['source_modules'][:-1];(run/'submission/REVIEW.json').write_text(json.dumps(review,indent=2)+'\n')
                elif kind=='nonstandard-axiom':
                    p=run/'submission/EXPORT.Direct.json';v=common.load(p);v['declarations'][0]['axioms'].append('Lean.ofReduceBool');p.write_text(json.dumps(v,indent=2)+'\n')
                elif kind=='primary-reclassification':review['primary_eligible']=True;(run/'submission/REVIEW.json').write_text(json.dumps(review,indent=2)+'\n')
                export=run/'submission';files=[dict(path=p.name,sha256=common.sha(p)) for p in sorted(export.iterdir()) if p.is_file() and p.name!='LOCK.json'];(export/'LOCK.json').write_text(json.dumps(dict(files=files),indent=2)+'\n');outer=common.load(run/'result.json');outer['artifact_export']['lock_sha256']=common.sha(export/'LOCK.json');(run/'result.json').write_text(json.dumps(outer,indent=2)+'\n')
                data=common.load(a.runs)
                for row in data['rows']:
                    if row['trial']==target['trial']:row['out']=str(run)
                runs=fixture/'RUNS.json';runs.write_text(json.dumps(data,indent=2)+'\n')
            receipt=a.out/(label+'.json');command=[sys.executable,*flags,str(HERE/'check_supplemental.py'),'--runs',str(runs),'--output',str(receipt)]
            result=subprocess.run(command,capture_output=True,text=True);(a.out/(label+'.stdout')).write_text(result.stdout);(a.out/(label+'.stderr')).write_text(result.stderr)
            common.need(result.returncode==0 if kind=='positive' else result.returncode!=0 and not receipt.exists(),'Actual acceptance CLI wrong result '+label)
            checks.append(dict(case=kind,optimization=opt,command=command,exitcode=result.returncode,stdout_sha256=common.sha(a.out/(label+'.stdout')),stderr_sha256=common.sha(a.out/(label+'.stderr'))))
            if fixture:
                common.need(fixture.parent==a.out and not fixture.is_symlink(),'Cleanup escaped owned fixture');shutil.rmtree(fixture)
    common.save(a.out/'RESULT.json',dict(status='PASS_ACTUAL_ALL13_VALIDATOR_NORMAL_O_OO_AND12_NEGATIVE_REJECTIONS',positive_routes=3,negative_rejections=12,checks=checks,validator_sha256=common.sha(HERE/'check_supplemental.py'),controller_sha256=common.sha(Path(__file__)),original_evidence_modified=False,regenerable_fixture_directories_cleaned=True))
    print('PASS actual3positive+12negative supplemental validator routes')

if __name__=='__main__':main()
