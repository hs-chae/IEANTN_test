#!/usr/bin/env python3
"""Actual portable controller/leaf CLIs in normal/-O/-OO with fresh objects."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--application-build',type=Path,required=True);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--cpu',type=int,default=16);a=p.parse_args()
    out=a.out.resolve();need(out.is_relative_to(a.application_build.resolve())and not out.exists(),'fresh baseline-owned output');out.mkdir();controller=S/'scripts/execute_demand_manifest_context.py';helper=S/'scripts/compile_lean_context.py';d=json.loads(a.manifest.read_text());need(d['queries']==[1000,367],'separate fixed tiny test universe');records=[]
    for mode in ['normal','O','OO']:
        prefix=[sys.executable]+([]if mode=='normal'else['-'+mode])
        for case,extra,accept in [('good',['--expected-pi','1000=168','--expected-pi','367=73'],True),('wrong-count',['--expected-pi','1000=169','--expected-pi','367=73'],False),('missing-query',['--expected-pi','1000=168'],False),('memory',['--expected-pi','1000=168','--expected-pi','367=73','--memory-gib','301'],False),('workers',['--expected-pi','1000=168','--expected-pi','367=73','--jobs','33'],False)]:
            target=out/(mode+'-'+case);cmd=prefix+[str(controller),'--context',str(a.context),'--application-build',str(a.application_build),'--manifest',str(a.manifest),'--out',str(target),'--jobs','1','--memory-gib','24','--cpus',str(a.cpu)]+extra
            t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);log=out/(mode+'-'+case+'.json');log.write_text(json.dumps(dict(command=cmd,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');need((r.returncode==0)==accept,'portable actual acceptance '+mode+' '+case)
            if accept:
                result=json.loads((target/'RESULT.json').read_text());need(result['status']=='COMPLETED_HOST_KERNEL_CERTIFICATE_PIPELINE_NOT_ISOLATED_NOT_C_SOURCE_PV'and result['controller_final_theorem_audit']is not None,'complete fresh exact theorem audit')
            else:need(not target.exists(),'negative route fails before execution output')
            records.append(dict(mode=mode,case=case,expected_acceptance=accept,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log),sha256=sha(log)))
        runtime=a.application_build/'NUMERICAL_CONTEXT.json'
        for case,context,accept in [('good',runtime,True),('duplicate-json',out/(mode+'-duplicate-context.json'),False)]:
            if not accept:context.write_text('{"compiler":"a","compiler":"b"}\n')
            leaf=out/(mode+'-leaf-'+case);cmd=prefix+[str(helper),d['namespace']+'.Check0000','--context',str(context),'--source-root',d['source_root'],'--audit-root',str(leaf),'--memory-gib','24','--cpus',str(a.cpu)]
            t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);log=out/(mode+'-leaf-'+case+'.json');log.write_text(json.dumps(dict(command=cmd,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');need((r.returncode==0)==accept,'actual leaf parser '+mode+' '+case)
            if not accept:need(not leaf.exists(),'duplicate JSON fails before compiler')
            records.append(dict(mode=mode,case='leaf-'+case,expected_acceptance=accept,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log),sha256=sha(log)))
    result=dict(status='PASS_PORTABLE_ACTUAL_CONTROLLER_AND_LEAF_CLIS_NORMAL_O_OO',controller_sha256=sha(controller),helper_sha256=sha(helper),context_sha256=sha(a.context),fresh_baseline_receipt_sha256=sha(a.application_build/'RESULT.json'),records=records)
    tmp=out/'RESULT.json.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(out/'RESULT.json');print(json.dumps(dict(status=result['status'],routes=len(records),out=str(out))))
if __name__=='__main__':main()
