#!/usr/bin/env python3
"""Actual optimization-safe sealed-evidence CLI controls with owned temporary copies."""
import argparse,json,shutil,subprocess,sys
from pathlib import Path
import run_review as common
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--bundle',required=True,type=Path);ap.add_argument('--out',required=True,type=Path);args=ap.parse_args()
    common.need(not args.out.exists(),'Fresh control directory required');args.out.mkdir(parents=True);records=[]
    for opt in [0,1,2]:
        flags=[] if opt==0 else ['-O'] if opt==1 else ['-OO']
        for case in ['positive','source-mutation','primary-promotion','missing-locked-file']:
            label=case+'-'+str(opt);fixture=None;bundle=args.bundle
            if case!='positive':
                fixture=args.out/(label+'-fixture');shutil.copytree(args.bundle,fixture);bundle=fixture
                manifest=common.load(fixture/'MANIFEST.json')
                if case=='source-mutation':
                    path=next((fixture/'locked_payloads').rglob('*.lean'));path.write_bytes(path.read_bytes()+b'\n-- mutation\n')
                elif case=='primary-promotion':
                    manifest['new_primary_successes']=13;(fixture/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
                else:next((fixture/'locked_payloads').rglob('*.lean')).unlink()
            receipt=args.out/(label+'.json');command=[sys.executable,*flags,str(HERE/'verify_supplemental_bundle.py'),'--bundle',str(bundle),'--output',str(receipt)]
            result=subprocess.run(command,capture_output=True,text=True)
            (args.out/(label+'.stdout')).write_text(result.stdout);(args.out/(label+'.stderr')).write_text(result.stderr)
            common.need(result.returncode==0 and receipt.is_file() if case=='positive' else result.returncode!=0 and not receipt.exists(),'Actual sealed CLI control failed '+label)
            records.append(dict(case=case,optimization=opt,command=command,returncode=result.returncode,stdout_sha256=common.sha(args.out/(label+'.stdout')),stderr_sha256=common.sha(args.out/(label+'.stderr'))))
            if fixture:
                common.need(fixture.parent==args.out and not fixture.is_symlink(),'Cleanup escaped owned fixture');shutil.rmtree(fixture)
    common.save(args.out/'RESULT.json',dict(status='PASS_SEALED_BUNDLE_ACTUAL_NORMAL_O_OO_CONTROLS',records=records,positive=3,rejections=9,
                validator_sha256=common.sha(HERE/'verify_supplemental_bundle.py'),controller_sha256=common.sha(Path(__file__)),
                original_evidence_unchanged=True,owned_regenerable_fixtures_cleaned=True))
    print('PASS actual3positive+9negative sealed-bundle CLI controls')


if __name__=='__main__':main()
