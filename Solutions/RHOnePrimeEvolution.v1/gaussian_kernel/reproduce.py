#!/usr/bin/env python3
"""Regenerate the fixed Gaussian numerical certificates and freshly compile their Lean consumers."""
import argparse,hashlib,json,os,pathlib,re,subprocess,sys,time

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def run(command,log):
 with log.open('w') as stream:
  result=subprocess.run(command,stdout=stream,stderr=subprocess.STDOUT)
 if result.returncode:
  raise RuntimeError('Command failed (exit '+str(result.returncode)+'); inspect '+str(log))

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--run',required=True);ap.add_argument('--jobs',type=int,default=2);ap.add_argument('--compiler');ap.add_argument('--generic-lean-path');ap.add_argument('--regenerate-only',action='store_true');args=ap.parse_args()
 if args.jobs<1 or args.jobs>8:raise ValueError('--jobs must lie in1..8; admit against live host capacity')
 here=pathlib.Path(__file__).resolve().parent;repo=here.parents[2];out=pathlib.Path(args.run).resolve()
 if out.exists():raise ValueError('Refusing to overwrite existing experiment directory '+str(out))
 out.mkdir(parents=True);start=time.time()
 commands=[]
 cmd=[sys.executable,str(here/'prototype_cells.py'),'--candidate',str(here/'CANDIDATE_DEGREE12.json'),'--out',str(out/'partition.json')];commands.append(cmd);run(cmd,out/'partition.log')
 cmd=[sys.executable,str(here/'generate_kernel_cells.py'),'--candidate',str(here/'CANDIDATE_DEGREE12.json'),'--partition',str(out/'partition.json'),'--output',str(out/'regenerated'),'--chunk-size','72'];commands.append(cmd);run(cmd,out/'generation.log')
 rows=[]
 for generated in sorted((out/'regenerated').glob('*.lean')):
  actual=here/generated.name
  if not actual.is_file():raise FileNotFoundError('Missing committed proof source '+str(actual))
  same=generated.read_bytes()==actual.read_bytes();rows.append({'module':generated.stem,'regenerated_sha256':sha(generated),'committed_sha256':sha(actual),'exact_match':same})
  if not same:raise ValueError('Certificate regeneration differs: '+generated.name)
 if len(rows)!=9:raise ValueError('Expected exactly9 regenerated Lean source files, received '+str(len(rows)))
 manifest={'status':'REGENERATION_PASS_NOT_LEAN_ACCEPTANCE','commands':commands,'candidate_sha256':sha(here/'CANDIDATE_DEGREE12.json'),'source_generator_sha256':sha(here/'generate_kernel_cells.py'),'partition_generator_sha256':sha(here/'prototype_cells.py'),'generated_sources':rows,'python':sys.version,'random_seeds':'none; deterministic exact rational regeneration','seconds':time.time()-start}
 (out/'REGENERATION.json').write_text(json.dumps(manifest,indent=2)+'\n')
 if args.regenerate_only:
  print(json.dumps({'status':manifest['status'],'run':str(out),'seconds':manifest['seconds']}));return
 cmd=[sys.executable,str(here.parent/'scripts'/'rebuild_closure.py'),'--repository',str(repo),'--run',str(out/'lean'),'--source-dir',str(here),'--roots','GaussianNumericalAudit','--jobs',str(args.jobs)]
 if args.compiler:cmd+=['--compiler',args.compiler]
 if args.generic_lean_path:cmd+=['--generic-lean-path',args.generic_lean_path]
 commands.append(cmd);run(cmd,out/'lean-driver.log')
 execution_path=out/'lean'/'EXECUTION.json'
 result=json.load(open(execution_path))
 if result.get('status')!='PASS_FRESH_TRANSITIVE_COMPILATION':raise ValueError('Fresh replay did not pass')
 if result.get('compiled_modules')!=result.get('required_modules'):raise ValueError('Fresh replay is incomplete')
 if result.get('roots')!=['GaussianNumericalAudit']:raise ValueError('Wrong replay consumer')
 if any(row.get('returncode')!=0 for row in result.get('builds',[])):raise ValueError('A compiler did not succeed')
 audit_logs=list((out/'lean'/'logs').glob('GaussianNumericalAudit.stdout'))
 if len(audit_logs)!=1:raise ValueError('Expected exactly one final axiom audit log')
 audit=audit_logs[0].read_text()
 for forbidden in ['sorryAx','ofReduceBool','Lean.trustCompiler','Lean.ofReduceBool']:
  if forbidden in audit:raise ValueError('Forbidden execution/admission axiom in final audit: '+forbidden)
 expected={'RHOnePrime.GaussianKernel.'+name for name in ['cellValid_integral_upper','coeff_gaussian_infinite_tail','norm_finite_integral','wing_finite_integral','physical_norm_upper','physical_full_wings_upper','physicalF_zero_lower','physical_full_objective_upper','physical_full_objective_lt_printed_2026']}
 found=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",audit,re.S)
 if len(found)!=9 or {name for name,_ in found}!=expected:raise ValueError('Wrong final axiom audit identities/count')
 for name,raw in found:
  axioms={x.strip() for x in raw.split(',') if x.strip()}
  if not axioms<= {'propext','Classical.choice','Quot.sound'}:raise ValueError('Unapproved theorem axiom closure: '+name+' '+str(axioms))
 manifest['status']='PASS_REGENERATED_CERTIFICATES_AND_FRESH_LEAN_REPLAY';manifest['commands']=commands;manifest['fresh_receipt_sha256']=sha(execution_path);manifest['seconds']=time.time()-start
 (out/'REPRODUCTION.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps({'status':manifest['status'],'run':str(out),'seconds':manifest['seconds']}))
if __name__=='__main__':
 try:main()
 except Exception as error:
  print(type(error).__name__+': '+str(error),file=sys.stderr);sys.exit(1)
