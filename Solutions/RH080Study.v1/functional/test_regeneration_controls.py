#!/usr/bin/env python3
"""Execute actual regeneration CLIs against wrong inputs in normal/-O/-OO modes.

Full successful real-input regeneration is separately required in every mode.
The small negative fixtures deliberately omit large cells: each rejection must
name the intended early guard, and may not publish an acceptance receipt.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,shutil,time

def need(c,msg):
 if not c:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--family',choices=['primal28','primal40'],required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();here=Path(__file__).resolve().parent;src=here/a.family
 need(not a.out.exists(),'Fresh controls output required');a.out.mkdir(parents=True);start=time.monotonic();rows=[]
 cases=['existing_output','inside_source','candidate_hash','coefficient_identity','missing_candidate','unknown_cli']
 if a.family=='primal28':cases.append('original_source_hash')
 for mode in ['', '-O','-OO']:
  for case in cases:
   run=a.out/((mode or 'normal').replace('-','')+'_'+case);work=run/'fixture';own=work/a.family;own.mkdir(parents=True)
   for n in ['regenerate.py','CANDIDATE_LAGUERRE28.json' if a.family=='primal28' else'CANDIDATE_LAGUERRE40.json','PARTITION.json','COEFFICIENTS_EXACT.json','CELL_SOURCE_MANIFEST.json']+(['OPT28_ORIGINAL.json']if a.family=='primal28'else[]):shutil.copy2(src/n,own/n)
   generic=work/'primal40';generic.mkdir(exist_ok=True)
   for n in ['generate_kernel_cells.py','prototype_cells.py']:shutil.copy2(here/'primal40'/n,generic/n)
   out=run/'output';expected='';extra=[];cand=own/('CANDIDATE_LAGUERRE28.json' if a.family=='primal28' else'CANDIDATE_LAGUERRE40.json')
   if case=='existing_output':out.mkdir();expected='--out must be a fresh directory'
   elif case=='inside_source':out=own/'new_output';expected='scratch must be outside publishable source'
   elif case=='candidate_hash':cand.write_bytes(cand.read_bytes()+b' ');expected='candidate SHA mismatch'
   elif case=='coefficient_identity':
    f=own/'COEFFICIENTS_EXACT.json';d=json.loads(f.read_text());d['norm'][0]='2';f.write_text(json.dumps(d));expected='exact Laguerre transform coefficient mismatch'
   elif case=='missing_candidate':cand.unlink();expected='FileNotFoundError'
   elif case=='unknown_cli':extra=['--unsupported-mode'];expected='unrecognized arguments'
   elif case=='original_source_hash':
    f=own/'OPT28_ORIGINAL.json';f.write_bytes(f.read_bytes()+b' ');expected='original timely input SHA mismatch'
   cmd=[sys.executable]+([mode]if mode else[])+[str(own/'regenerate.py'),'--out',str(out)]+extra
   r=subprocess.run(cmd,capture_output=True,text=True);(run/'stdout.txt').write_text(r.stdout);(run/'stderr.txt').write_text(r.stderr)
   accepted=out/'REGENERATION_RECEIPT.json';valid=r.returncode!=0 and expected in r.stderr and not accepted.exists()
   rows.append({'mode':mode or'normal','case':case,'command':cmd,'returncode':r.returncode,'expected_guard':expected,'guard_observed':expected in r.stderr,'acceptance_receipt_absent':not accepted.exists(),'passed':valid,'stdout_sha256':sha(run/'stdout.txt'),'stderr_sha256':sha(run/'stderr.txt')})
   need(valid,'Guard failure '+str(rows[-1]))
 result={'status':'PASS_ACTUAL_NEGATIVE_REGENERATION_CLI_ALL_OPTIMIZATION_MODES','family':a.family,'cases':len(rows),'scope':'Early rejection controls only. Complete positive regeneration is recorded separately in all three modes.','rows':rows,'seconds':time.monotonic()-start,'script_sha256':sha(Path(__file__)),'wrapper_sha256':sha(src/'regenerate.py')};pending=a.out/'RESULT.pending';pending.write_text(json.dumps(result,indent=2)+'\n');pending.rename(a.out/'RESULT.json');print(result['status'],len(rows))
if __name__=='__main__':main()
