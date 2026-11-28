#!/usr/bin/env python3
"""Bounded all-mode controls for exact source selection; never create an archive."""
import argparse,json,os,subprocess,sys
from pathlib import Path
from bootstrap_context import atomic,need,read_json,sha
HERE=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',required=True,type=Path);ap.add_argument('--run',required=True,type=Path)
    ap.add_argument('--proof-plan',action='append',default=[])
    a=ap.parse_args();need(not os.path.lexists(a.run),'Fresh bundle control output required');a.run.mkdir(parents=True)
    selector=HERE/'select_source_bundle.py';source_sha=sha(selector);cases=[]
    common=['--context',str(a.context)]
    for value in a.proof_plan:common+=['--proof-plan',value]
    def invoke(mode,label,args,success,manifest=False):
        cmd=[sys.executable]+{'normal':[],'O':['-O'],'OO':['-OO']}[mode]+[str(selector)]+args
        out=a.run/(mode+'-'+label+'.stdout');err=a.run/(mode+'-'+label+'.stderr')
        with out.open('xb')as o,err.open('xb')as e:r=subprocess.run(cmd,stdout=o,stderr=e,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        need((r.returncode==0)is success,'Unexpected bundle CLI outcome '+mode+'/'+label)
        if manifest:
            target=Path(args[args.index('--out')+1]);value=read_json(target/'SOURCE_BUNDLE_MANIFEST.json')
            need(value['status']=='INCOMPLETE_SOURCE_SELECTION_NO_FINAL_BUNDLE_ACCEPTANCE'
                and len(value['locked_payloads'])==16 and value['unresolved'],'Pending source selection was overstated')
        cases.append(dict(mode=mode,case=label,command=cmd,returncode=r.returncode,
            stdout_sha256=sha(out),stderr_sha256=sha(err)))
    for mode in ['normal','O','OO']:
        invoke(mode,'help',['--help'],True)
        invoke(mode,'actual-pending-manifest',common+['--out',str(a.run/(mode+'-selection'))],True,True)
        invoke(mode,'required-complete-rejection',common+['--out',str(a.run/(mode+'-required')),'--require-complete'],False,True)
        invoke(mode,'existing-output',common+['--out',str(a.run)],False)
        invoke(mode,'unknown-option',['--conte',str(a.context)],False)
        invoke(mode,'unknown-family',common+['--out',str(a.run/(mode+'-badfamily')),'--proof-plan','unrequested=/absent'],False)
    need(sha(selector)==source_sha,'Selector changed during actual controls')
    atomic(a.run/'RESULT.json',dict(status='PASS_SOURCE_SELECTOR_ACTUAL_PENDING_UNIVERSE_AND_FAIL_CLOSED_CLIS_ALL_MODES',
        selector_sha256=source_sha,controller_sha256=sha(Path(__file__)),cases=cases,positive=6,negative=12,
        final_source_bundle_accepted=False,archive_created=False))
    print('PASS exact source selector:6 positive/12 rejection controls,normal/-O/-OO')
if __name__=='__main__':main()
