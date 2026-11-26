#!/usr/bin/env python3
"""Actual all-mode format export and hardlink/schema checks; no new proof claim."""
import argparse,json,os,subprocess,sys
from pathlib import Path
from reproduce_dual import need,load,sha,publish
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in['base','context','candidate','accepted','out']:ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh export controls required');a.out.mkdir(parents=True);records=[]
    for opt in[0,1,2]:
        flags=[]if opt==0 else ['-O']if opt==1 else ['-OO'];out=a.out/('export-'+str(opt));command=[sys.executable,*flags,str(HERE/'export_fft_dag_bank.py'),'--base',str(a.base),'--context',str(a.context),'--candidate',str(a.candidate),'--accepted',str(a.accepted),'--run',str(out),'--toy']
        p=subprocess.run(command,capture_output=True,text=True);(a.out/('positive-'+str(opt)+'.stdout')).write_text(p.stdout);(a.out/('positive-'+str(opt)+'.stderr')).write_text(p.stderr);need(p.returncode==0,'Actual format exporter failed')
        plan=load(out/'PLAN.json');need(len(plan['source_rows'])==120 and plan['compile_phases']==dict(original=118,prior_continuation=1,current_fresh=1),'Format identities/phases changed')
        for row in plan['source_rows']:
            name=row['module'];receipt=load(out/(name+'.COMPILED.json'));need(receipt['exitcode']==receipt['returncode']==0 and receipt['original_compiler_receipt_sha256']==sha(Path(receipt['original_compiler_receipt'])),'Normalized actual receipt differs')
            for source,target in[(a.base/'objects'/(name.replace('.','/')+'.olean'),out/'objects'/(name.replace('.','/')+'.olean')),(a.base/'sources'/(name.replace('.','/')+'.lean'),Path(row['snapshot']))]:
                need(os.stat(source).st_ino==os.stat(target).st_ino and os.stat(source).st_dev==os.stat(target).st_dev,'Large artifact copied instead of hardlinked')
        records.append(dict(case='format-only-positive',optimization=opt,command=command,returncode=p.returncode,result_sha256=sha(out/'RESULT.json')))
        bad=a.out/('wrong-acceptance-'+str(opt)+'.json');data=load(a.accepted);data['result_sha256']='0'*64;bad.write_text(json.dumps(data,indent=2)+'\n');rejected=a.out/('must-not-create-'+str(opt));command=[sys.executable,*flags,str(HERE/'export_fft_dag_bank.py'),'--base',str(a.base),'--context',str(a.context),'--candidate',str(a.candidate),'--accepted',str(bad),'--run',str(rejected),'--toy'];v=subprocess.run(command,capture_output=True,text=True);(a.out/('negative-'+str(opt)+'.stderr')).write_text(v.stderr);need(v.returncode!=0 and not rejected.exists(),'Unaccepted proof bank exported');records.append(dict(case='wrong-independent-acceptance',optimization=opt,command=command,returncode=v.returncode))
    publish(a.out/'RESULT.json',dict(status='PASS_ACTUAL_FORMAT_EXPORT_NORMAL_O_OO_SCHEMA_HARDLINKS_AND3_REJECTIONS',records=records,positive=3,rejections=3,
        exporter_sha256=sha(HERE/'export_fft_dag_bank.py'),controller_sha256=sha(Path(__file__)),new_mathematical_proof=False,large_artifacts_not_copied=True))
    print('PASS3actual format exports+3rejections; exact normalized schema/hardlinks')


if __name__=='__main__':main()
