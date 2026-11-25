#!/usr/bin/env python3
"""Exercise actual replay CLI guards and exact theorem types under normal/-O/-OO.

Rejected mutated theorem types show only that the accepted proof does not prove
the changed statement; they are never reported as mathematical counterexamples.
"""
import argparse, hashlib, json, os, subprocess, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
def need(ok,message):
    if not ok:raise RuntimeError(message)
def main():
    parser=argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--accepted',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--context',type=Path,default=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json'))
    args=parser.parse_args();need(not args.out.exists(),'Fresh controls directory required')
    need((args.accepted/'RESULT.json').is_file(),'Actual accepted replay required')
    args.out.mkdir(parents=True)
    context=json.loads(args.context.read_text());bad=dict(context);bad['compiler_sha256']='0'*64
    badcontext=args.out/'bad-compiler-context.json';badcontext.write_text(json.dumps(bad)+'\n')
    env=os.environ.copy();env['LEAN_PATH']=str(args.accepted/'objects')+':'+context['generic_lean_path']
    cases=[]
    for flags,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
        for name,extra,expected in [
          ('existing-output',['--out',str(args.accepted)],'Fresh output directory required'),
          ('bad-compiler',['--out',str(args.out/(label+'-rejected-run')),'--context',str(badcontext)],'Compiler identity differs')]:
            command=[sys.executable,*flags,str(HERE/'reproduce.py'),*extra]
            run=subprocess.run(command,capture_output=True,text=True)
            need(run.returncode!=0 and expected in run.stderr,'CLI rejection failed '+label+':'+name)
            cases.append(dict(case=label+':'+name,returncode=run.returncode,expected_rejection=True,command=command))
    prefix='import Primal80ActualFourier\nopen scoped FourierTransform\nopen RH080.Primal80Fourier RHOnePrime.GaussianFourier\n'
    snippets={
      'positive':('example : 𝓕 (fun x : ℝ => (RH080.Gaussian40.physicalF x : ℂ)) = fun x : ℝ => (RH080.Gaussian40.physicalG x : ℂ) := fourier_actual_physical\n',True),
      'wrong-output':('example : 𝓕 (fun x : ℝ => (RH080.Gaussian40.physicalF x : ℂ)) = fun x : ℝ => (RH080.Gaussian40.physicalG x : ℂ)+1 := fourier_actual_physical\n',False),
      'changed-coefficient':('example : evenTransform normEvenSource = RHOnePrime.GaussianKernel.coeffPoly (RH080.Gaussian40.wingSource++[1]) := actual_even_transform\n',False),
    }
    for name,(body,accepted) in snippets.items():
        source=args.out/(name.replace('-','_')+'.lean');source.write_text(prefix+body)
        command=[context['compiler'],'-j2',str(source)]
        run=subprocess.run(command,env=env,capture_output=True,text=True)
        (args.out/(name+'.stdout')).write_text(run.stdout);(args.out/(name+'.stderr')).write_text(run.stderr)
        need((run.returncode==0)==accepted,'Exact type control failed '+name)
        cases.append(dict(case=name,returncode=run.returncode,expected_acceptance=accepted,command=command))
    need(not list(args.out.glob('*rejected-run/RESULT.json')),'Rejected replay published acceptance')
    result=dict(status='PASS_OPTIMIZATION_SAFE_CLI_AND_EXACT_TYPE_CONTROLS',cases=cases,controls_prove_only_contract_rejection=True)
    pending=args.out/'RESULT.pending';pending.write_text(json.dumps(result,indent=2)+'\n');os.link(pending,args.out/'RESULT.json');pending.unlink()
    print(json.dumps(dict(status=result['status'],cases=len(cases))))
if __name__=='__main__':main()
