#!/usr/bin/env python3
"""Bounded actual associated-proof controls under an owned300GiB/noSwap unit."""
import argparse,json,subprocess,sys
from pathlib import Path
from compile_verified_batch_linked_v2 import read_json,need,atomic,sha
HERE=Path(__file__).resolve().parent


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context','bank','out']:ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();need(not a.out.exists(),'Fresh bounded control destination required');a.out.mkdir()
    rows=[]
    for mode in range(3):
        flags=['-'+'O'*mode]if mode else[]
        base=[sys.executable,*flags,str(HERE/'compile_verified_batch_linked_v2.py'),
           '--context',str(a.context),'--bank',str(a.bank),'--root','review.AnalyticFlatAsymptoticRootAudit',
           '--memory-gib','300','--worker-virtual-as','unlimited']
        run=a.out/('positive-'+str(mode));command=[*base,'--run',str(run)]
        p=subprocess.run(command,capture_output=True,text=True)
        (a.out/('positive-'+str(mode)+'.stdout')).write_text(p.stdout);(a.out/('positive-'+str(mode)+'.stderr')).write_text(p.stderr)
        need(p.returncode==0 and (run/'RESULT.json').is_file(),'Actual bounded associated proof failed')
        plan=read_json(run/'PLAN.json');result=read_json(run/'RESULT.json')
        need(plan['per_compiler_AS_bytes']is None and result['per_compiler_AS_bytes']is None,
             'Associated proof retained finite virtual-AS cap')
        need(result['source_cold']is False and result['source_first_PV_complete']is False,
             'Associated proof mislabeled complete source-first PV')
        need(len(plan['source_rows'])==1,'Expected exactly one fresh audit root')
        compiled=read_json(run/'review.AnalyticFlatAsymptoticRootAudit.COMPILED.json')
        need('--as=unlimited'in compiled['command'],'Actual fresh compiler lacked unlimited AS')
        for child in plan['accepted_dependencies']:
            obj=run/'objects'/(child['module'].replace('.','/')+'.olean');origin=Path(child['object_origin'])
            need(obj.stat().st_ino==origin.stat().st_ino and obj.stat().st_dev==origin.stat().st_dev,
                 'Accepted object was copied rather than immutably linked')
            need(sha(obj)==child['object_sha256'],'Accepted object changed')
        rows.append(dict(case='positive',mode=mode,command=command,returncode=p.returncode,
             result_sha256=sha(run/'RESULT.json'),new_modules=1,accepted_modules=len(plan['accepted_dependencies'])))
        for case in ['missing-virtual-policy','numeric-virtual-policy','wrong-physical-declaration',
                     'unknown-root','missing-bank','existing-destination']:
            cmd=list(base);bad=a.out/(case+'-'+str(mode))
            if case=='missing-virtual-policy':
                i=cmd.index('--worker-virtual-as');del cmd[i:i+2]
            elif case=='numeric-virtual-policy':cmd[cmd.index('--worker-virtual-as')+1]='300'
            elif case=='wrong-physical-declaration':cmd[cmd.index('--memory-gib')+1]='299'
            elif case=='unknown-root':cmd[cmd.index('--root')+1]='MissingActualSource'
            elif case=='missing-bank':cmd[cmd.index('--bank')+1]=str(a.out/'NO_BANK')
            else:bad=run
            cmd+=['--run',str(bad)];q=subprocess.run(cmd,capture_output=True,text=True)
            need(q.returncode!=0 and (case=='existing-destination'or not(bad/'RESULT.json').exists()),
                 'Associated compiler accepted invalid CLI '+case)
            rows.append(dict(case=case,mode=mode,command=cmd,returncode=q.returncode))
        for case in ['missing-virtual-policy','wrong-physical-declaration']:
            bad=a.out/('wrapper-'+case+'-'+str(mode));cmd=[sys.executable,*flags,str(HERE/'reproduce_w4_main_v2.py'),
                '--context',str(a.context),'--bank',str(a.bank),'--run',str(bad),'--memory-gib','300',
                '--worker-virtual-as','unlimited']
            if case=='missing-virtual-policy':del cmd[-2:]
            else:cmd[cmd.index('--memory-gib')+1]='299'
            q=subprocess.run(cmd,capture_output=True,text=True)
            need(q.returncode!=0 and not(bad/'W4_MAIN_ACCEPTANCE.json').exists(),'Final wrapper admitted invalid policy')
            rows.append(dict(case='wrapper-'+case,mode=mode,command=cmd,returncode=q.returncode))
    atomic(a.out/'RESULT.json',dict(status='PASS_LINKED_V2_3_ACTUAL_FRESH_AUDITS_24_CLI_REJECTIONS',
            records=rows,helper_sha256=sha(HERE/'compile_verified_batch_linked_v2.py'),
            wrapper_sha256=sha(HERE/'reproduce_w4_main_v2.py'),harness_sha256=sha(Path(__file__)),
            full_W4_wrapper_positive_executed=False,source_cold=False,whole_PV_claimed=False))
    print('PASS associated unlimited-AS:3 fresh proof audits +24 CLI rejections')
if __name__=='__main__':main()
