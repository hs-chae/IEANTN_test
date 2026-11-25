#!/usr/bin/env python3
"""Actual Lean exact-contract and consumed-premise mutations; no Python assert."""
import argparse,hashlib,json,os,subprocess,sys,tempfile,time
from pathlib import Path

def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--objects',type=Path,required=True);p.add_argument('--run',type=Path,required=True);a=p.parse_args();need(not a.run.exists(),'Fresh controls directory required');a.run.mkdir(parents=True);c=json.loads(a.context.read_text());env=os.environ.copy();env['LEAN_PATH']=str(a.objects.resolve(strict=True))+':'+c['generic_lean_path'];prefix='import EarlySolution\nset_option autoImplicit false\nopen Real\n';actual='ThetaCubePopulation.v3.challenge_cube_density_096699_from_369 hRH hS h₁ h₂';args='(hRH:RH.v1.hypothesis) (hS:SchoenfeldRHTheta.v1.refined_theta) (h₁:Buthe.v1.theorem_2_theta) (h₂:Buthe.v1.theorem_2_theta_lower)';cases=[]
 cases.append(('positive_exact',prefix+f'example {args} : ThetaCubePopulation.v3.cube_density_096699_from_369 := {actual}\n',True,None))
 for name,coef,onset in [('wrong_coefficient','967/1000','369'),('wrong_onset','96699/100000','368')]:
  text=prefix+f'example {args} : ∀ n:ℝ,{onset}≤n → ({coef}:ℝ)*n^2/log n < ((IEANTN.ThetaWindows.openPrimes (n^3) ((n+1)^3)).card:ℝ) := {actual}\n';cases.append((name,text,False,'Type mismatch'))
 text=prefix+'example (hRH:RH.v1.hypothesis) (hS:SchoenfeldRHTheta.v1.refined_theta) : ThetaCubePopulation.v3.cube_density_096699_from_369 := ThetaCubePopulation.v3.challenge_cube_density_096699_from_369 hRH hS\n';cases.append(('missing_finite_sources',text,False,'Type mismatch'))
 text=prefix+f'example {args} : ∀ n:ℝ,369≤n → (96699/100000:ℝ)*n^2/log n < ((IEANTN.ThetaWindows.openPrimes (n^3+1) ((n+1)^3)).card:ℝ) := {actual}\n';cases.append(('changed_lower_endpoint',text,False,'Type mismatch'))
 text='''import Lean
import EarlySolution
open Lean Elab Command
theorem unused_source (h:Buthe.v1.theorem_2_theta) : True := True.intro
run_cmd do
 let env←getEnv
 let some (.thmInfo t):=env.find? `unused_source | throwError "Missing fixture"
 match t.value with
 | .lam _ _ b _ => unless b.hasLooseBVar 0 do throwError "REJECT_REQUIRED_SOURCE_INPUT_NOT_CONSUMED"
 | _ => throwError "Malformed fixture"
''';cases.append(('unused_source_argument',text,False,'REJECT_REQUIRED_SOURCE_INPUT_NOT_CONSUMED'));rows=[]
 for name,text,want,guard in cases:
  source=a.run/(name+'.lean');source.write_text(text);cmd=['/usr/bin/prlimit','--as='+str(32*2**30),'--',c['compiler'],'-j2',str(source)];t=time.monotonic();r=subprocess.run(cmd,env=env,capture_output=True);(a.run/(name+'.stdout')).write_bytes(r.stdout);(a.run/(name+'.stderr')).write_bytes(r.stderr);need((r.returncode==0)==want,'Unexpected actual Lean control result '+name)
  if guard:need(guard in r.stdout.decode(),'Wrong rejection path '+name)
  need('unknown constant' not in r.stdout.decode().lower(),'Missing import caused control failure')
  rows.append(dict(name=name,command=cmd,returncode=r.returncode,expected_success=want,required_guard=guard,seconds=time.monotonic()-t,source_sha256=sha(source),stdout_sha256=sha(a.run/(name+'.stdout')),stderr_sha256=sha(a.run/(name+'.stderr'))))
 result=dict(status='PASS_ACTUAL_LEAN_MATHEMATICAL_CONTRACT_AND_SOURCE_USAGE_CONTROLS',python_optimization=sys.flags.optimize,cases=rows,controller_sha256=sha(Path(__file__)),compiler_sha256=sha(Path(c['compiler'])),meaning='Mutation rejection establishes exact accepted contracts/consumedsource checks, not impossibility of the mutated mathematical claim.')
 fd,name=tempfile.mkstemp(dir=a.run,prefix='.acceptance-');q=Path(name)
 try:
  with os.fdopen(fd,'w') as f:json.dump(result,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(q,a.run/'RESULT.json')
 finally:q.unlink()
 print(json.dumps(dict(status=result['status'],cases=len(rows),optimization=sys.flags.optimize)))
if __name__=='__main__':main()
