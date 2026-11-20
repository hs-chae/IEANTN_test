#!/usr/bin/env python3
"""Run real normal/-O/-OO controller routes with fixed accepted small data."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve()
    need(out.is_relative_to(Path('/data/ivy-ramanujan-source-pv-20261119'))and not out.exists(),'fresh owned output');out.mkdir(parents=True)
    base=Path('/data/ivy-ramanujan-source-pv-20261119/demand-small-pair-v1');controller=S/'scripts/execute_demand_manifest_parallel.py';records=[]
    for mode in ['normal','O','OO']:
        prefix=[sys.executable]+([]if mode=='normal'else['-'+mode])+[str(controller)]
        for case,extra,accept in [('good',['--expected-pi','1000=168','--expected-pi','367=73'],True),('wrong-count',['--expected-pi','1000=169','--expected-pi','367=73'],False),('missing-query',['--expected-pi','1000=168'],False),('memory',['--expected-pi','1000=168','--expected-pi','367=73','--memory-gib','301'],False),('workers',['--expected-pi','1000=168','--expected-pi','367=73','--jobs','33'],False)]:
            target=out/(mode+'-'+case);cmd=prefix+['--manifest',str(base/'PROPOSAL.json'),'--out',str(target),'--jobs','1','--memory-gib','24','--cpus','20','--import-audit',str(base/'parallel-controller-test-v1/audit'),'--import-audit',str(base/'parallel-controller-test-v2/audit')]+extra
            start=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);log=out/(mode+'-'+case+'.json');log.write_text(json.dumps(dict(command=cmd,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n')
            need((r.returncode==0)==accept,'actual CLI acceptance '+mode+' '+case)
            if accept:
                result=json.loads((target/'RESULT.json').read_text());need(result['status']=='COMPLETED_HOST_KERNEL_CERTIFICATE_PIPELINE_NOT_ISOLATED_NOT_C_SOURCE_PV'and result['controller_final_theorem_audit']is not None,'actual complete trusted theorem audit')
            else:need(not target.exists(),'negative route fails before any output/compilation')
            records.append(dict(mode=mode,case=case,expected_acceptance=accept,returncode=r.returncode,seconds=time.monotonic()-start,receipt=str(log),sha256=sha(log)))
    receipt=dict(status='PASS_ACTUAL_CLIS_NORMAL_O_OO',controller_sha256=sha(controller),records=records)
    tmp=out/'RESULT.json.pending';tmp.write_text(json.dumps(receipt,indent=2)+'\n');tmp.replace(out/'RESULT.json');print(json.dumps(dict(status=receipt['status'],routes=len(records),out=str(out))))
if __name__=='__main__':main()
