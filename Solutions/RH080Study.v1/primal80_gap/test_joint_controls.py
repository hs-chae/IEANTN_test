#!/usr/bin/env python3
"""Actual CLI and theorem-contract controls for the complete v2 source replay.

Rejection of a changed theorem type is not a mathematical counterexample.
"""
import argparse, hashlib, json, os, subprocess, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
def need(ok,message):
    if not ok:raise RuntimeError(message)
def read(p):
    def pairs(items):
        out={}
        for key,value in items:
            need(key not in out,'Duplicate JSON key');out[key]=value
        return out
    return json.loads(p.read_bytes(),object_pairs_hook=pairs,
        parse_constant=lambda x:(_ for _ in ()).throw(ValueError('Non-finite JSON constant: '+x)))
def main():
    parser=argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--accepted',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--context',type=Path,default=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json'))
    args=parser.parse_args();need(not args.out.exists(),'Fresh controls directory required')
    need((args.accepted/'RESULT.json').is_file(),'Completed actual joint source replay required')
    args.out.mkdir(parents=True);context=read(args.context)
    bad=dict(context);bad['compiler_sha256']='0'*64
    bad_context=args.out/'bad_context.json';bad_context.write_text(json.dumps(bad)+'\n')
    # A bounded fixture preserves actual source/log associations but deliberately
    # omits every cell object, so the explicit new-cell-bank route is exercised.
    fixture_base=args.accepted.resolve(strict=True)
    cold_fixture=args.out/'cold_without_cells';cold_fixture.mkdir()
    (cold_fixture/'PLAN.json').write_bytes((fixture_base/'PLAN.json').read_bytes())
    os.symlink((fixture_base/'source').resolve(),cold_fixture/'source',target_is_directory=True)
    for folder in ['objects','logs']:
        (cold_fixture/folder).mkdir()
        for entry in (fixture_base/folder).rglob('*'):
            if not entry.is_file() or entry.name.startswith('G40Cells'):continue
            target=cold_fixture/folder/entry.relative_to(fixture_base/folder)
            target.parent.mkdir(parents=True,exist_ok=True);os.symlink(entry.resolve(),target)
    # Deliberately invalid object metadata is assembled solely from this fresh
    # accepted run. It must fail at the actual object-hash guard before any
    # purported batch certificate is read or any compiler can execute.
    plan=read(fixture_base/'PLAN.json')
    bank_rows=[]
    for row in plan['modules']:
        module=row['module']
        if not module.startswith('G40Cells'):continue
        source=fixture_base/'source'/(module+'.lean')
        obj=fixture_base/'objects'/(module+'.olean')
        need(source.is_file() and obj.is_file(),'Fresh accepted cell provider missing')
        need(hashlib.sha256(source.read_bytes()).hexdigest()==row['source_sha256'],'Fresh captured cell source differs')
        bank_rows.append(dict(module=module,source=str(source),source_sha256=row['source_sha256'],
            object=str(obj),object_sha256='0'*64,batch_receipt=str(fixture_base/'PLAN.json')))
    need(len(bank_rows)==25,'Fresh accepted cell population differs')
    bank=dict(status='ALL25_NEW_DEGREE80_CELL_MODULES_1193_CELLS_COMPILED_SOURCE_OBJECT_IDENTITIES_MATCH',
        rows=bank_rows,fixture='INTENTIONALLY_INVALID_OBJECT_HASH_NOT_AN_ACCEPTED_CERTIFICATE')
    bad_bank=args.out/'bad_new_cell_bank.json';bad_bank.write_text(json.dumps(bank)+'\n')
    cases=[]
    for flags,label in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
        for key,options,message in [
          ('existing-output',['--out',str(args.accepted)],'Fresh output directory required'),
          ('bad-compiler',['--out',str(args.out/(label+'-bad-compiler')),'--context',str(bad_context)],'Compiler identity differs'),
          ('excess-aggregate-memory',['--out',str(args.out/(label+'-excess-memory')),'--workers','8','--worker-memory-gib','64'],'Aggregate compiler address-space allowance exceeds authorized256GiB'),
          ('bank-without-compound',['--out',str(args.out/(label+'-bank-without-compound')),'--accepted-new-cell-bank',str(bad_bank)],'New cell bank is only permitted with an explicit compound cold-leaf repair'),
          ('bad-bank-object',['--out',str(args.out/(label+'-bad-bank-object')),'--reuse-cold-leaves',str(cold_fixture),'--accepted-new-cell-bank',str(bad_bank)],'New-cell object differs')]:
            command=[sys.executable,*flags,str(HERE/'reproduce_joint.py'),'--context',str(args.context),'--lean-cert-source',str(HERE.parents[2]/'Solutions/RHOnePrimeEvolution.v1/gaussian_gap/portable/source'),*options]
            run=subprocess.run(command,capture_output=True,text=True)
            (args.out/(label+'-'+key+'.stdout')).write_text(run.stdout)
            (args.out/(label+'-'+key+'.stderr')).write_text(run.stderr)
            need(run.returncode!=0 and message in run.stderr,'CLI control failed '+label+':'+key)
            cases.append(dict(case=label+':'+key,returncode=run.returncode,expected_rejection=True,command=command))
    env=os.environ.copy();env['LEAN_PATH']=str(args.accepted/'objects')+':'+context['generic_lean_path']
    prefix='import Primal80ActualConsumers\nopen IEANTN.CMSFunctional\nopen RH080.Primal80Gap\n'
    statements={
      'positive-exact-source-type':('example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis → EventualGapBound (2746403660/3293251743 : ℝ) := actual_normalized_gap\n',True),
      'missing-general-source':('example : RH.v1.hypothesis → RHAsymptoticGaussian.v2.normalized_gap := actual_normalized_gap\n',False),
      'missing-raw-witness':('example : GaussianFourierWitness.v2.objective_witness := GaussianFourierWitness.v2.challenge_objective_witness\n',False),
      'changed-exact-gap':('example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis → EventualGapBound (8339/10000 : ℝ) := actual_normalized_gap\n',False),
      'removed-width-slack':('example (hCMS : CMSFunctionalInput.v1.population_reduction) (rh : RH.v1.hypothesis) : ∀ α : ℝ, 0 ≤ α → GoodCoefficient α ((2746403660/3293251743 : ℝ)*(1+2*α)) := actual_population_curve hCMS rh\n',False)}
    for key,(body,accept) in statements.items():
        source=args.out/(key.replace('-','_')+'.lean');source.write_text(prefix+body)
        command=[context['compiler'],'-j2',str(source)]
        run=subprocess.run(command,env=env,capture_output=True,text=True)
        (args.out/(key+'.stdout')).write_text(run.stdout);(args.out/(key+'.stderr')).write_text(run.stderr)
        need((run.returncode==0)==accept,'Exact theorem type control failed '+key)
        cases.append(dict(case=key,returncode=run.returncode,expected_acceptance=accept,command=command))
    for key in ['normal','O','OO']:
        for suffix in ['bad-compiler','excess-memory','bank-without-compound','bad-bank-object']:
            need(not (args.out/(key+'-'+suffix)/'RESULT.json').exists(),'Rejected child published acceptance')
    result=dict(status='PASS_JOINT_CLI_OPTIMIZATION_AND_MATHEMATICAL_CONTRACT_CONTROLS',cases=cases,changed_theorem_rejections_are_not_counterexamples=True)
    temporary=args.out/'RESULT.pending';temporary.write_text(json.dumps(result,indent=2)+'\n');os.link(temporary,args.out/'RESULT.json');temporary.unlink()
    print(json.dumps(dict(status=result['status'],cases=len(cases))))
if __name__=='__main__':main()
