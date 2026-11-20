#!/usr/bin/env python3
"""Actual full-scalar validator CLIs under normal/-O/-OO, no assert acceptance."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--accepted-result',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'fresh controls');a.out.mkdir(parents=True);original=json.loads(a.accepted_result.read_text());rows=[]
 for mode,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
  for case in ['valid','duplicate-json','missing-child','axiom-population','wrong-axioms','count-promotion','PV-promotion']:
   result=json.loads(json.dumps(original))
   if case=='missing-child':result['records'].pop()
   if case=='axiom-population':result['records'][-1]['required_constants']=[];result['records'][-1]['axioms']={}
   if case=='wrong-axioms':result['records'][-1]['axioms']={result['records'][-1]['required_constants'][0]:['Lean.ofReduceBool']}
   if case=='count-promotion':result['prime_counts_formally_proved_here']=True
   if case=='PV-promotion':result['source_first_PV']=True
   path=a.out/(label+'-'+case+'.json');text=json.dumps(result)
   if case=='duplicate-json':text=text.replace('{','{"status":"bad",',1)
   path.write_text(text);cmd=[sys.executable,*mode,str(S/'scripts/execute_full_scalar_certificate.py'),'--check',str(path)];run=subprocess.run(cmd,capture_output=True,text=True);(a.out/(label+'-'+case+'.stdout')).write_text(run.stdout);(a.out/(label+'-'+case+'.stderr')).write_text(run.stderr);need((run.returncode==0)==(case=='valid'),'actual CLI verdict '+case);rows.append({'mode':mode,'case':case,'returncode':run.returncode,'command':cmd,'stdout_sha256':hashlib.sha256(run.stdout.encode()).hexdigest(),'stderr_sha256':hashlib.sha256(run.stderr.encode()).hexdigest()})
 out={'status':'PASS','actual_cli_controls':len(rows),'controller_sha256':hashlib.sha256((S/'scripts/execute_full_scalar_certificate.py').read_bytes()).hexdigest(),'records':rows};(a.out/'RESULT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':'PASS','actual_cli_controls':len(rows)}))
if __name__=='__main__':main()
