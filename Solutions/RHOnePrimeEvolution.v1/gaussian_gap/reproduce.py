#!/usr/bin/env python3
"""Regenerate the complete selected Gaussian Lean source proof and ANT consumers.
Requires the pinned Lean toolchain and generic dependency cache; no accepted
application .olean or generated numerical dataset is required.
"""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--repository',type=Path,required=True);p.add_argument('--run',type=Path,required=True);p.add_argument('--jobs',type=int,default=2,choices=(1,2,3,4));p.add_argument('--compiler',type=Path);p.add_argument('--generic-lean-path');a=p.parse_args()
 R=a.repository.resolve(strict=True);S=R/'Solutions/RHOnePrimeEvolution.v1';D=a.run.resolve();controller=D.with_name(D.name+'-controller');acceptance=D.with_name(D.name+'-acceptance')
 if any(p.exists() for p in (D,controller,acceptance)):raise SystemExit('Fresh run/controller/acceptance destinations required')
 C=json.loads((S/'scripts/LOCAL_CONTEXT.json').read_text());compiler=a.compiler
 if compiler is None:
  pinned=Path(C['compiler']);compiler=pinned if pinned.is_file() else Path(subprocess.check_output(['elan','which','lean'],cwd=R,text=True).strip())
 compiler=compiler.resolve(strict=True);version=subprocess.check_output([str(compiler),'--version'],text=True)
 expected=(R/'lean-toolchain').read_text().strip().split(':v')[-1]
 if expected not in version:raise SystemExit('Pinned Lean version mismatch')
 dependencies={x['name']:x for x in C['generic_dependency_versions']};names=[x['name'] for x in C['generic_dependency_versions'] if x['library_present']]
 own=[R/'.lake/packages'/n/'.lake/build/lib/lean' for n in names]
 generic=a.generic_lean_path or (':'.join(map(str,own)) if all(x.is_dir() for x in own) else C['mathlib_lean_path'])
 for item in generic.split(':'):
  library=Path(item)
  if not library.is_dir() or len(library.parents)<4:raise SystemExit('Restore pinned generic library '+item)
  package=library.parents[3];name=package.name
  if name not in dependencies:raise SystemExit('Only known pinned generic package libraries permitted '+item)
  revision=subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip()
  clean=subprocess.check_output(['git','-C',str(package),'status','--porcelain','--untracked-files=no'],text=True)
  if revision!=dependencies[name]['revision'] or clean:raise SystemExit('Generic source version/cleanliness mismatch '+name)
 controller.mkdir(parents=True)
 for name in ('rebuild_closure.py','BASELINE_IMPORTS.json','LOCAL_CONTEXT.json'):
  q=controller/name;q.write_bytes((S/'scripts'/name).read_bytes());q.chmod(0o444)
 command=['python3',str(controller/'rebuild_closure.py'),'--repository',str(R),'--run',str(D),'--include-core','--compiler',str(compiler),'--generic-lean-path',generic]
 for part in ('gaussian_kernel','gaussian_fourier','gaussian_gap'):command+=['--source-dir',str(S/part)]
 for alias,family in [('GaussianFourierWitnessSolution','GaussianFourierWitness'),('RHAsymptoticGaussianSolution','RHAsymptoticGaussian')]:command+=['--module-file',alias+'='+str(R/'Solutions'/(family+'.v1')/'Solution.lean')]
 command+=['--roots','GaussianCanonicalAudit','GaussianAsymptoticConsumers','GaussianFourierWitnessSolution','RHAsymptoticGaussianSolution','--jobs',str(a.jobs)]
 print('Frozen source-only proof build:',json.dumps(command),flush=True)
 result=subprocess.run(command,cwd=R)
 if result.returncode:raise SystemExit(result.returncode)
 verify=['python3',str(S/'gaussian_gap/verify_fresh.py'),'--repository',str(R),'--build',str(D),'--out',str(acceptance)]
 raise SystemExit(subprocess.run(verify,cwd=R).returncode)
if __name__=='__main__':main()
