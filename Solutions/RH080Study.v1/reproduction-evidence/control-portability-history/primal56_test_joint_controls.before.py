#!/usr/bin/env python3
"""Actual CLI and theorem-contract controls for the complete v3 source replay.

Rejection of a changed theorem type is not a mathematical counterexample.
"""
import argparse, json, os, subprocess, sys
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
    need((args.accepted/'RESULT.json').is_file(),'Completed actual joint source replay required')
    args.out.mkdir(parents=True);context=json.loads(args.context.read_text())
    bad=dict(context);bad['compiler_sha256']='0'*64
    bad_context=args.out/'bad_context.json';bad_context.write_text(json.dumps(bad)+'\n')
    cases=[]
    for flags,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
        for key,options,message in [
          ('existing-output',['--out',str(args.accepted)],'Fresh output directory required'),
          ('bad-compiler',['--out',str(args.out/(label+'-bad-compiler')),'--context',str(bad_context)],'Compiler identity differs'),
          ('excess-aggregate-memory',['--out',str(args.out/(label+'-excess-memory')),'--workers','8'],'invalid choice')]:
            command=[sys.executable,*flags,str(HERE/'reproduce_joint.py'),*options]
            run=subprocess.run(command,capture_output=True,text=True)
            (args.out/(label+'-'+key+'.stdout')).write_text(run.stdout)
            (args.out/(label+'-'+key+'.stderr')).write_text(run.stderr)
            need(run.returncode!=0 and message in run.stderr,'CLI control failed '+label+':'+key)
            cases.append(dict(case=label+':'+key,returncode=run.returncode,expected_rejection=True,command=command))
    env=os.environ.copy();env['LEAN_PATH']=str(args.accepted/'objects')+':'+context['generic_lean_path']
    prefix='import Primal56ActualConsumers\nopen IEANTN.CMSFunctional\nopen RH080.Primal56Gap\n'
    statements={
      'positive-exact-source-type':('example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis → EventualGapBound (82325773717/98718416336 : ℝ) := actual_normalized_gap\n',True),
      'missing-general-source':('example : RH.v1.hypothesis → RHAsymptoticGaussian.v3.normalized_gap := actual_normalized_gap\n',False),
      'missing-raw-witness':('example : GaussianFourierWitness.v3.objective_witness := GaussianFourierWitness.v3.challenge_objective_witness\n',False),
      'changed-exact-gap':('example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis → EventualGapBound (8339/10000 : ℝ) := actual_normalized_gap\n',False),
      'removed-width-slack':('example (hCMS : CMSFunctionalInput.v1.population_reduction) (rh : RH.v1.hypothesis) : ∀ α : ℝ, 0 ≤ α → GoodCoefficient α ((82325773717/98718416336 : ℝ)*(1+2*α)) := actual_population_curve hCMS rh\n',False)}
    for key,(body,accept) in statements.items():
        source=args.out/(key.replace('-','_')+'.lean');source.write_text(prefix+body)
        command=[context['compiler'],'-j2',str(source)]
        run=subprocess.run(command,env=env,capture_output=True,text=True)
        (args.out/(key+'.stdout')).write_text(run.stdout);(args.out/(key+'.stderr')).write_text(run.stderr)
        need((run.returncode==0)==accept,'Exact theorem type control failed '+key)
        cases.append(dict(case=key,returncode=run.returncode,expected_acceptance=accept,command=command))
    for key in ['normal','O','OO']:
        for suffix in ['bad-compiler','excess-memory']:
            need(not (args.out/(key+'-'+suffix)/'RESULT.json').exists(),'Rejected child published acceptance')
    result=dict(status='PASS_JOINT_CLI_OPTIMIZATION_AND_MATHEMATICAL_CONTRACT_CONTROLS',cases=cases,changed_theorem_rejections_are_not_counterexamples=True)
    temporary=args.out/'RESULT.pending';temporary.write_text(json.dumps(result,indent=2)+'\n');os.link(temporary,args.out/'RESULT.json');temporary.unlink()
    print(json.dumps(dict(status=result['status'],cases=len(cases))))
if __name__=='__main__':main()
