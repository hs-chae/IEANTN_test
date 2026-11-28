#!/usr/bin/env python3
"""Bounded actual positive/negative CLI controls for the linked batch helper."""
import argparse,json,os,subprocess,sys
from pathlib import Path
from bootstrap_context import atomic,need,read_json,sha
HERE=Path(__file__).resolve().parent
HELPER=HERE.parent/'pv/compile_verified_batch_linked.py'
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['context','bank','run']:ap.add_argument('--'+name,required=True,type=Path)
    ap.add_argument('--root',default='AnalyticFlatFamilyAsymptoticAudit')
    a=ap.parse_args();need(not os.path.lexists(a.run),'Fresh controls directory required');a.run.mkdir(parents=True)
    helper_sha=sha(HELPER);context=read_json(a.context);cases=[]
    bad=dict(context,compiler_sha256='0'*64);atomic(a.run/'bad-compiler.json',bad)
    (a.run/'duplicate-context.json').write_text('{"compiler":"x","compiler":"y"}')
    (a.run/'nonfinite-context.json').write_text('{"compiler":NaN}')
    wrong=a.run/'wrong-context-bank';wrong.mkdir();atomic(wrong/'PLAN.json',dict(context_sha256='0'*64,source_rows=[]))
    def invoke(mode,label,arguments,success,artifact=None):
        prefix=[sys.executable]+({'normal':[],'O':['-O'],'OO':['-OO']}[mode])+[str(HELPER)]
        cmd=prefix+list(map(str,arguments));out=a.run/(mode+'-'+label+'.stdout');err=a.run/(mode+'-'+label+'.stderr')
        with out.open('xb')as o,err.open('xb')as e:r=subprocess.run(cmd,stdout=o,stderr=e,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        need((r.returncode==0)is success,'Unexpected linked-helper outcome: '+mode+'/'+label)
        if artifact:
            plan=read_json(artifact/'PLAN.json');result=read_json(artifact/'RESULT.json')
            need(result['status']=='PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY'and plan['roots']==[a.root]
                and plan['immutable_dependency_objects_hardlinked']is True,'Fresh linked proof scope differs')
            need('sorryAx'not in(artifact/'logs'/(a.root+'.stdout')).read_text(),'Nonstandard proof axiom diagnostic')
        cases.append(dict(mode=mode,case=label,expected_success=success,returncode=r.returncode,
            command=cmd,stdout_sha256=sha(out),stderr_sha256=sha(err)))
    for mode in ['normal','O','OO']:
        invoke(mode,'help',['--help'],True)
        target=a.run/(mode+'-positive');base=['--context',a.context,'--bank',a.bank,'--root',a.root,'--memory-gib','32']
        invoke(mode,'actual-proof',base+['--run',target],True,target)
        invoke(mode,'unknown-option',['--conte',a.context],False)
        invoke(mode,'existing-output',base+['--run',target],False)
        invoke(mode,'bad-compiler',['--context',a.run/'bad-compiler.json','--bank',a.bank,'--root',a.root,'--run',a.run/(mode+'-bad-compiler')],False)
        for label in ['duplicate','nonfinite']:
            invoke(mode,label+'-json',['--context',a.run/(label+'-context.json'),'--bank',a.bank,'--root',a.root,'--run',a.run/(mode+'-'+label)],False)
        invoke(mode,'wrong-bank-context',['--context',a.context,'--bank',wrong,'--root',a.root,'--run',a.run/(mode+'-wrong-bank')],False)
        invoke(mode,'missing-source-root',base+['--run',a.run/(mode+'-missing-source'),'--source-root',a.run/'nonexistent-source'],False)
    need(sha(HELPER)==helper_sha,'Linked helper changed during actual controls')
    atomic(a.run/'RESULT.json',dict(status='PASS_CURRENT_LINKED_HELPER_ACTUAL_PROOF_AND_NEGATIVE_CLIS_ALL_MODES',
        helper_sha256=helper_sha,context_sha256=sha(a.context),controller_sha256=sha(Path(__file__)),
        cases=cases,positive=6,negative=21,full_source_cold=False,whole_campaign_acceptance=False))
    print('PASS current linked helper: 3 actual fresh proofs, 3 help, 21 negative CLI controls')
if __name__=='__main__':main()
