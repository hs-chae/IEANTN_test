#!/usr/bin/env python3
"""Actual normal/-O/-OO CLI checks of frozen EXTERNAL arithmetic routines.
These controls establish reproducibility/validator behavior, not analytic
soundness, a Lean certificate, or source-first program verification.
"""
from pathlib import Path
import argparse,json,subprocess,hashlib,time
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--python',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
if a.out.exists():raise SystemExit('Fresh output required')
a.out.mkdir(parents=True);b=Path(__file__).resolve().parent;frozen=b/'external-certifiers-frozen-v1';rows=[];start=time.monotonic()
basew=b/'hat-witnesses/asymp-m100.json';bad=json.loads(basew.read_text());bad['threshold']='0';badfile=a.out/'wrong-threshold.json';badfile.write_text(json.dumps(bad)+'\n')
expect={};modes=[[],['-O'],['-OO']]
for i,mode in enumerate(modes):
 root=a.out/f'mode{i}';root.mkdir()
 routes=[('gaussian','certify_gaussian_objective.py',['--candidate',str(b/'seeds/A36over11-degree20.json'),'--A','36/11'],True,'PASS_DIRECTED_ARB_AND_EXACT_STURM_WRITTEN_IDENTITIES_NOT_LEAN_OR_PV'),('fourier','check_fourier_gaussian.py',['--candidate',str(b/'seeds/A36over11-degree20.json')],True,'PASS_EXACT_MONOMIAL_FOURIER_IDENTITY_AND_7_DIRECT_ARB_INTEGRALS'),('hat','certify_hat_witness.py',['--witness',str(basew)],True,'PASS_DIRECTED_ARB_EXACT_HAT_OBJECTIVE_NOT_LEAN_OR_PV'),('bad-grid','certify_hat_witness.py',['--witness',str(basew),'--grid','1001'],False,'invalid grid/source parameters'),('wrong-threshold','certify_hat_witness.py',['--witness',str(badfile)],False,'FAIL_TARGET_OBJECTIVE')]
 for name,script,args,success,reason in routes:
  out=root/name;cmd=[a.python,*mode,str(frozen/script),*args,'--out',str(out)];t=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True)
  (root/(name+'.stdout')).write_text(r.stdout);(root/(name+'.stderr')).write_text(r.stderr)
  if success:
   if r.returncode:raise RuntimeError('positive route failed '+name+' mode'+str(i))
   data=json.loads((out/'RESULT.json').read_text())
   if data['status']!=reason:raise RuntimeError('wrong positive status')
   semantic=data.get('enclosures',data.get('rows'))
   if name not in expect:expect[name]=semantic
   elif semantic!=expect[name]:raise RuntimeError('optimization changed numerical result '+name)
  else:
   if r.returncode==0:raise RuntimeError('negative case accepted')
   result=out/'RESULT.json'
   if result.exists():
    if json.loads(result.read_text()).get('status')!=reason:raise RuntimeError('wrong negative reason')
   elif reason not in r.stderr:raise RuntimeError('wrong CLI failure reason')
  rows.append({'name':name,'mode':mode,'command':cmd,'returncode':r.returncode,'seconds':time.monotonic()-t,'expected_success':success,'reason':reason,'validator_sha256':hashlib.sha256((frozen/script).read_bytes()).hexdigest()})
rec={'status':'PASS_15_ACTUAL_CLI_ROUTES_ALL3_OPTIMIZATION_MODES','seconds':time.monotonic()-start,'rows':rows,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'External arithmetic repeatability and negative-case behavior only; notLean/PV/analytic proof'}
(a.out/'RESULT.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],rec['seconds'])
