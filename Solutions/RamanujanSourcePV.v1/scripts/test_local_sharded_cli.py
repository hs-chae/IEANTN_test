#!/usr/bin/env python3
"""Current-byte sharded audit routes including fresh O/OO compilation."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh controls');out.mkdir(parents=True);base=Path('/data/ivy-ramanujan-source-pv-20261119/local-window-cli56-v1');script=S/'scripts/execute_local_window_sharded_audit.py';progress=base/'reuse-controller-fresh-normal-v2/PROGRESS.json';d=json.loads(progress.read_text());d['records'][0]['receipt_sha256']='0'*64;bad=out/'bad-progress.json';bad.write_text(json.dumps(d,indent=2)+'\n');duplicate=out/'duplicate.json';duplicate.write_text('{"schema":"a","schema":"b"}\n');records=[]
 for mode in ['normal','O','OO']:
  prefix=[sys.executable]+([]if mode=='normal'else['-'+mode])+[str(script)]
  for case,extra,accept in [('good',[],True),('wrong-width',['--width','57'],False),('bad-receipt',['--progress',str(bad)],False),('bad-shard',['--shard-size','2049'],False),('workers',['--jobs','9'],False),('memory',['--memory-gib','97'],False),('duplicate-json',['--manifest',str(duplicate)],False)]:
   target=out/(mode+'-'+case);cmd=prefix+['--manifest',str(base/'PROPOSAL.json'),'--progress',str(progress),'--out',str(target),'--width','56','--jobs','1','--memory-gib','24','--cpus','16']+extra;t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);log=out/(mode+'-'+case+'.json');log.write_text(json.dumps(dict(command=cmd,returncode=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');need((r.returncode==0)==accept,'actual current sharded CLI '+mode+' '+case)
   if accept:
    d=json.loads((target/'RESULT.json').read_text());need(d['status']=='COMPLETED_HOST_LOCAL_KERNEL_INCREMENT_PROOFS_BASE_PAIR_PENDING_NOT_SOURCE_PV_ALONE'and d['exact_prime_types_checked']==16 and d['sharded_exact_type_and_aggregate_axiom_audit']is True and d['controller_sha256']==sha(script),'complete exact fresh audit')
   else:need(not(target/'RESULT.json').exists(),'no acceptance after rejection')
   records.append(dict(mode=mode,case=case,expected_acceptance=accept,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log),sha256=sha(log)))
 result=dict(status='PASS_LOCAL_SHARDED_AUDIT_ACTUAL_CLIS_NORMAL_O_OO',controller_sha256=sha(script),records=records);tmp=out/'RESULT.json.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(out/'RESULT.json');print(json.dumps(dict(status=result['status'],routes=len(records),out=str(out))))
if __name__=='__main__':main()
