#!/usr/bin/env python3
"""Run the fixed analytic-transition count proposal; never marks it a proof."""
from pathlib import Path
import datetime,hashlib,json,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def main():
 if len(sys.argv)!=2:raise ValueError('one fresh absolute output directory required')
 out=Path(sys.argv[1]);
 if not out.is_absolute() or out.exists():raise ValueError('fresh absolute output')
 out.mkdir(parents=True)
 source=S/'scripts/generate_demand_certificate_resources.py'
 command=['/usr/bin/time','-v','-o',str(out/'rusage.txt'),sys.executable,str(source),'--queries','1490000000000','--name','HighTransitionCount','--out',str(out/'proposal'),'--cpus','48,49,50,51','--memory-gib','256','--max-records','300000000']
 identity=sha(source);start=time.monotonic()
 with (out/'stdout').open('wb') as stdout,(out/'stderr').open('wb') as stderr:
  process=subprocess.Popen(command,stdout=stdout,stderr=stderr)
  live={'status':'ACTUALLY_RUNNING_UNTRUSTED_COUNT_PROPOSAL','pid':process.pid,'started':datetime.datetime.now(datetime.timezone.utc).isoformat(),'command':command,'generator_sha256':identity}
  (out/'RUNNING.json').write_text(json.dumps(live,indent=2)+'\n');code=process.wait()
 proposal=out/'proposal/PROPOSAL.json';result=dict(live,returncode=code,elapsed_seconds=time.monotonic()-start,source_unchanged=sha(source)==identity,status='UNTRUSTED_PROPOSAL_COMPLETE_NOT_FORMAL_ACCEPTANCE' if code==0 and proposal.is_file() else 'PROPOSAL_RESOURCE_OR_IMPLEMENTATION_FAILURE_RETAINED',rusage_sha256=sha(out/'rusage.txt'),stdout_sha256=sha(out/'stdout'),stderr_sha256=sha(out/'stderr'),native_output_not_a_Lean_fact=True)
 if proposal.is_file():
  q=json.loads(proposal.read_text());result.update(proposal_sha256=sha(proposal),records=q['records'],packed_bytes=q['packed_bytes'],results=q['results'])
 (out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
 if code:sys.exit(1)
if __name__=='__main__':main()
