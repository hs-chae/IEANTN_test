#!/usr/bin/env python3
"""Accept the exact fresh Gaussian source closure and real mathematical controls.
No asserts: acceptance is invariant under Python normal/-O/-OO modes.
"""
import argparse,hashlib,json,os,re,subprocess,time
from pathlib import Path

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(path,value):
 temporary=path.with_name(path.name+'.tmp')
 with temporary.open('x') as f:json.dump(value,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
 os.replace(temporary,path);fd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
 try:os.fsync(fd)
 finally:os.close(fd)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--repository',type=Path,required=True);p.add_argument('--build',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 R=a.repository.resolve(strict=True);B=a.build.resolve(strict=True);D=a.out.resolve();S=R/'Solutions/RHOnePrimeEvolution.v1'
 if D.exists():raise SystemExit('Fresh acceptance directory required')
 receipt=json.loads((B/'EXECUTION.json').read_text());plan=json.loads((B/'PLAN.json').read_text())
 if receipt['status']!='PASS_FRESH_TRANSITIVE_COMPILATION' or receipt['failure'] is not None:raise SystemExit('Fresh closure did not pass')
 if receipt['compiled_modules']!=receipt['required_modules'] or receipt['required_modules']!=len(plan['modules']):raise SystemExit('Incomplete source closure')
 if plan['predecessor_application_objects_used'] is not False:raise SystemExit('Predecessor application objects prohibited')
 if sha(B/'PLAN.json')!=receipt['PLAN_sha256']:raise SystemExit('Plan receipt hash mismatch')
 built={x['module']:x for x in receipt['builds']};selected={x['module']:x for x in plan['modules']}
 if len(built)!=len(receipt['builds']) or len(selected)!=len(plan['modules']) or set(built)!=set(selected):raise SystemExit('Compiled module identities inconsistent')
 for module,row in selected.items():
  if sha(Path(row['executed']))!=row['source_sha256'] or sha(Path(row['origin']))!=row['source_sha256']:raise SystemExit('Executed/current source mismatch '+module)
  result=built[module]
  if result['returncode']!=0:raise SystemExit('Failed module '+module)
  if sha(B/'objects'/(module.replace('.','/')+'.olean'))!=result['object_sha256']:raise SystemExit('Compiled object hash mismatch '+module)
  for stream in ('stdout','stderr'):
   if sha(B/'logs'/(module+'.'+stream))!=result[stream+'_sha256']:raise SystemExit('Compiler evidence hash mismatch '+module)
 if 'GaussianCanonicalAudit' not in selected:raise SystemExit('Final canonical audit missing')
 audit=(B/'logs/GaussianCanonicalAudit.stdout').read_text()
 if 'GAUSSIAN_CANONICAL_AUDIT_PASS roots=11 edges=12' not in audit or 'sorryAx' in audit:raise SystemExit('Actual exact-type/value/axiom audit missing')
 compiler=Path(plan['compiler'])
 if sha(compiler)!=plan['compiler_sha256']:raise SystemExit('Compiler hash mismatch')
 D.mkdir();src=D/'source';logs=D/'logs';objects=D/'objects'
 for x in (src,logs,objects):x.mkdir()
 (D/'verify_fresh.executed.py').write_bytes(Path(__file__).read_bytes())
 env=os.environ.copy();env['LEAN_PATH']=':'.join([str(B/'objects')]+plan['generic_paths'])
 prefix='import GaussianCanonicalConsumers\nopen Real Filter IEANTN.CMSFunctional\n'
 cases={
 'RejectChangedGapCoefficient':prefix+'example : RHAsymptoticGaussian.v1.normalized_gap = EventualGapBound (834020/1000000 : ℝ) := rfl\n',
 'RejectMissingSourceReduction':prefix+'example : RH.v1.hypothesis → GaussianFourierWitness.v1.objective_witness → RHAsymptoticGaussian.v1.normalized_gap := RHAsymptoticGaussian.v1.challenge_normalized_gap\n',
 'RejectMissingNumericalWitness':prefix+'example : CMSFunctionalInput.v1.gap_reduction → RH.v1.hypothesis → RHAsymptoticGaussian.v1.normalized_gap := RHAsymptoticGaussian.v1.challenge_normalized_gap\n',
 'RejectClaimedExplicitOnset':prefix+'example : RHAsymptoticGaussian.v1.normalized_gap = (∀ n : ℕ, 1000 ≤ n → normalizedGap n ≤ (834021/1000000 : ℝ)) := rfl\n',
 'RejectRemovedWidthEpsilon':prefix+'example : RHAsymptoticGaussian.v1.population_curve = (∀ α : ℝ, 0 ≤ α → GoodCoefficient α ((834021/1000000 : ℝ)*(1+2*α))) := rfl\n'}
 original=B/'source/GaussianActualTransform.lean';text=original.read_text();needle='419430399999999148579363/419430400000000000000000'
 if text.count(needle)!=1:raise SystemExit('Expected unique actual Fourier coefficient locator missing')
 cases['RejectActualFourierCoefficientMutation']=text.replace(needle,'419430399999999148579364/419430400000000000000000',1)
 rows=[];start=time.monotonic()
 for name,content in cases.items():
  file=src/(name+'.lean');file.write_text(content);cmd=['/usr/bin/prlimit','--as=68719476736','--','/usr/bin/time','-v',str(compiler),'--root='+str(src),'-j1','-o',str(objects/(name+'.olean')),str(file)];began=time.monotonic()
  with (logs/(name+'.stdout')).open('wb') as out,(logs/(name+'.stderr')).open('wb') as err:proc=subprocess.run(cmd,env=env,stdout=out,stderr=err)
  stdout=(logs/(name+'.stdout')).read_text();low=stdout.lower()
  if proc.returncode==0 or 'error' not in low or any(t in low for t in ('unknown module prefix','unknown identifier','already declared')):raise SystemExit('Negative mathematical control was not validly rejected '+name)
  if name=='RejectActualFourierCoefficientMutation' and not any(t in low for t in ('unsolved goals','tactic','false')):raise SystemExit('Fourier coefficient mutation did not reach actual kernel arithmetic')
  rows.append(dict(name=name,command=cmd,returncode=proc.returncode,seconds=time.monotonic()-began,source_sha256=sha(file),stdout_sha256=sha(logs/(name+'.stdout')),stderr_sha256=sha(logs/(name+'.stderr'))))
 result=dict(status='PASS_FRESH_GAUSSIAN_SOURCE_TYPE_VALUE_AXIOM_AND_CONTROLS',compiled_modules=len(selected),canonical_headliners=6,axiom_value_audit_roots=11,actual_value_edges=12,
  negative_controls=rows,seconds=time.monotonic()-start,source_build_receipt_sha256=sha(B/'EXECUTION.json'),source_plan_sha256=sha(B/'PLAN.json'),audit_stdout_sha256=sha(B/'logs/GaussianCanonicalAudit.stdout'),compiler_sha256=sha(compiler),controller_sha256=sha(D/'verify_fresh.executed.py'),source_ledger_sha256=sha(S/'gaussian_gap/SOURCE_LEDGER.html'),
  original_actual_Fourier_coefficient_source_sha256=sha(original),scope='Fresh exact selected Gaussian/numerical/Fourier/core/canonical Solution source closure. General CMS B reductions remain external mathematical inputs; standard three axioms only in audited closures. No source-first PV, explicit onset, global best-known or optimality claim.')
 atomic(D/'ACCEPTANCE.json',result);print(json.dumps({k:result[k] for k in ('status','compiled_modules','canonical_headliners','seconds')}))
if __name__=='__main__':main()
