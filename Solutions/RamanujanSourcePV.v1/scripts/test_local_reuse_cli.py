#!/usr/bin/env python3
"""Actual fresh/reuse/reject routes under every Python optimization mode."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh test output');out.mkdir(parents=True);base=Path('/data/ivy-ramanujan-source-pv-20261119/local-window-cli56-v1');script=S/'scripts/execute_local_prime_window_reuse.py';good=base/'reuse-controller-normal-v1/PROGRESS.json';d=json.loads(good.read_text());bad=out/'bad-progress.json';d['records'][0]['receipt_sha256']='0'*64;bad.write_text(json.dumps(d,indent=2)+'\n');duplicate=out/'duplicate-manifest.json';duplicate.write_text('{"schema":"a","schema":"b"}\n');records=[]
 for mode in ['normal','O','OO']:
  prefix=[sys.executable]+([]if mode=='normal'else['-'+mode])+[str(script)]
  for case,extra,accept in [('good',['--reuse-progress',str(good)],True),('wrong-width',['--width','57','--reuse-progress',str(good)],False),('bad-receipt',['--reuse-progress',str(bad)],False),('workers',['--jobs','9'],False),('memory',['--memory-gib','97'],False),('duplicate-json',['--manifest',str(duplicate)],False)]:
   target=out/(mode+'-'+case);cmd=prefix+['--manifest',str(base/'PROPOSAL.json'),'--out',str(target),'--width','56','--jobs','1','--memory-gib','24','--cpus','16']+extra;t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);log=out/(mode+'-'+case+'.json');log.write_text(json.dumps(dict(command=cmd,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');need((r.returncode==0)==accept,'actual optimized acceptance '+mode+' '+case)
   if accept:
    result=json.loads((target/'RESULT.json').read_text());need(result['status']=='COMPLETED_HOST_LOCAL_KERNEL_INCREMENT_PROOFS_BASE_PAIR_PENDING_NOT_SOURCE_PV_ALONE'and len(result['reused_modules'])==14 and result['posthoc_recovery']is True and result['base_pair_closed_here']is False,'complete exact reusable-source control')
   else:need(not(target/'RESULT.json').exists(),'negative cannot publish acceptance')
   records.append(dict(mode=mode,case=case,expected_acceptance=accept,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log),sha256=sha(log)))
 result=dict(status='PASS_LOCAL_REUSE_ACTUAL_CLIS_NORMAL_O_OO',controller_sha256=sha(script),fixed_positive_manifest_sha256=sha(base/'PROPOSAL.json'),records=records);tmp=out/'RESULT.json.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(out/'RESULT.json');print(json.dumps(dict(status=result['status'],routes=len(records),out=str(out))))
if __name__=='__main__':main()
