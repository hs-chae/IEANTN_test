#!/usr/bin/env python3
"""Clean-directory native reproduction. Produces ordinary numerical evidence.
Never calls this unverified numerical computation source-first PV.
"""
import argparse, hashlib, json, os, pathlib, subprocess, sys, time
PIN='9eb78bc0d1c98129f464db287699532376f52950'
def run(cmd,out,cwd=None):
 t=time.monotonic()
 with (out.with_suffix('.stdout')).open('wb') as so,(out.with_suffix('.stderr')).open('wb') as se:p=subprocess.run(cmd,cwd=cwd,stdout=so,stderr=se)
 result={'command':list(map(str,cmd)),'exit_code':p.returncode,'wall_seconds':time.monotonic()-t}
 out.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
 if p.returncode:raise RuntimeError('failed command, see '+str(out))
 return result

def main():
 p=argparse.ArgumentParser();p.add_argument('--scratch',type=pathlib.Path,required=True);p.add_argument('--study',type=pathlib.Path,required=True);p.add_argument('--end',type=int,default=1490000000000);p.add_argument('--mode',choices=['actual','unit'],default='actual');p.add_argument('--skip-exhaustive-count-check',action='store_true');a=p.parse_args();s=pathlib.Path(__file__).resolve().parents[1];d=a.scratch.resolve();r=a.study.resolve()
 if d.exists() or r.exists():raise ValueError('both reproduction directories must be fresh')
 if d.name!='ivy-ramanujan-source-pv-20261119':raise ValueError('use fresh parent /.../ivy-ramanujan-source-pv-20261119')
 d.mkdir(parents=True,mode=0o700);(r/'evidence').mkdir(parents=True)
 # Local source location is preserved by symlinking only this exact Solution;
 # generated files never enter the source worktree.
 target=r/'network/Solutions';target.mkdir(parents=True);(target/s.name).symlink_to(s,target_is_directory=True)
 o=r/'evidence/reproduction-build';o.mkdir();deps=d/'vendor/primecount';deps.parent.mkdir()
 run(['git','clone','--no-checkout','https://github.com/kimwalisch/primecount.git',str(deps)],o/'clone')
 run(['git','checkout','--detach',PIN],o/'checkout',deps)
 actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=deps,text=True).strip()
 if actual!=PIN:raise ValueError('dependency commit')
 b=d/'primecount-build'
 run(['cmake','-S',str(deps),'-B',str(b),'-DCMAKE_BUILD_TYPE=Release','-DBUILD_PRIMESIEVE=ON','-DBUILD_SHARED_LIBS=OFF','-DBUILD_STATIC_LIBS=ON','-DBUILD_TESTS=OFF'],o/'cmake')
 run(['cmake','--build',str(b),'-j8'],o/'build')
 common=['g++','-std=c++17','-O3','-march=native','-Wall','-Wextra','-Wconversion','-Werror']
 for name in ['benchmark_quotient_pi','independent_finite_check']:
  run([*common,str(s/'c'/(name+'.cpp')),'-o',str(d/name)],o/name)
 run([*common,'-fopenmp','-I'+str(deps/'include'),'-I'+str(deps/'lib/primesieve/include'),str(s/'c/generate_finite.cpp'),str(b/'libprimecount.a'),str(b/'lib/primesieve/libprimesieve.a'),'-lpthread','-o',str(d/'generate_finite')],o/'generate_finite')
 run([sys.executable,str(s/'scripts/run_finite.py'),'--study',str(r),'--scratch',str(d),'--end',str(a.end),'--mode',a.mode],o/'run')
 name='finite-'+a.mode+'-'+str(a.end)
 run([sys.executable,str(s/'scripts/check_exact_cells.py'),'--study',str(r),'--scratch',str(d),'--run',name],o/'enclosures')
 if not a.skip_exhaustive_count_check:run([sys.executable,str(s/'scripts/check_finite_independent.py'),'--study',str(r),'--scratch',str(d),'--run',name],o/'independent')
 final={'status':'ORDINARY_NUMERICAL_REPRODUCTION_COMPLETE','source_first_PV':False,'end':a.end,'mode':a.mode,'random_seeds':None,'dependency_commit':PIN,'full_count_check':not a.skip_exhaustive_count_check,'compiler_version':subprocess.check_output(['g++','--version'],text=True),'source_hashes':{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((s/'c').glob('*'))}}
 (r/'evidence/REPRODUCTION.json').write_text(json.dumps(final,indent=2)+'\n');print(json.dumps(final,indent=2))
if __name__=='__main__':main()
