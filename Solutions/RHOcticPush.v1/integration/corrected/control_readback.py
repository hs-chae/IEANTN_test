#!/usr/bin/env python3
"""Actual CLI positive and evidence-mutation controls in normal/-O/-OO.
Only a fresh experiment-owned copy is mutated; the accepted run and foundation
are never written. The clean copied receipt first must pass before negatives.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parent

def need(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
from reproduce import read
def write(p,d):p.write_text(json.dumps(d,indent=2,allow_nan=False)+'\n')
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();run=a.run.resolve();out=a.out.resolve();need(run.is_dir()and(run/'RESULT.json').is_file(),'completed run required');need(not out.exists()and not out.is_relative_to(run),'fresh independent control output required');out.mkdir(parents=True);clone=out/'owned-copy';shutil.copytree(run,clone,symlinks=True);rows=[];script=HERE/'reproduce.py';env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
 def cli(label,mode,want):
  cmd=[sys.executable,*(['-'+mode]if mode else[]),str(script),'--verify',str(clone)];t=time.monotonic();cp=subprocess.run(cmd,env=env,capture_output=True,text=True);prefix=out/(label+'-'+(mode or'normal'));prefix.with_suffix('.stdout').write_text(cp.stdout);prefix.with_suffix('.stderr').write_text(cp.stderr);need((cp.returncode==0)==want,'unexpected actual CLI result:'+label+':'+mode);rows.append({'label':label,'mode':mode or'normal','command':cmd,'returncode':cp.returncode,'expected_accept':want,'seconds':time.monotonic()-t,'stdout_sha256':sha(prefix.with_suffix('.stdout')),'stderr_sha256':sha(prefix.with_suffix('.stderr'))})
 for mode in ['', 'O','OO']:cli('clean-relocated',mode,True)
 manifest=read(clone/'SOURCE_CLOSURE.executed.json');first=manifest['modules'][0]['module'];rel=first.replace('.','/')
 mutations=[('source',clone/'source'/(rel+'.lean')),('object',clone/'objects'/(rel+'.olean')),('stdout',clone/'logs'/(first+'.stdout')),('stderr',clone/'logs'/(first+'.stderr')),('controller',clone/'reproduce.executed.py'),('C-source',clone/'C-ram/verified_finite_log.c'),('C-output',clone/'C-ram/stdout'),('manifest',clone/'SOURCE_CLOSURE.executed.json')]
 for label,path in mutations:
  need(path.is_file()and not path.is_symlink(),'only regular owned control targets');before=path.read_bytes();path.write_bytes(before+b'\nMUTATION\n')
  for mode in ['', 'O','OO']:cli(label,mode,False)
  path.write_bytes(before)
 def struct_case(label,change):
  touched={};change(touched)
  try:
   for mode in ['', 'O','OO']:cli(label,mode,False)
  finally:
   for p,b in touched.items():p.write_bytes(b)
 def put(t,path,obj):
  t.setdefault(path,path.read_bytes());write(path,obj)
 def build_case(t,kind):
  bp=clone/'BUILD.json';b=read(bp)
  if kind=='missing-route':b['modules'].pop()
  elif kind=='nonzero-route':b['modules'][0]['returncode']=7
  elif kind=='boolean-route':b['modules'][0]['returncode']=False
  elif kind=='wrong-command':b['modules'][0]['command'][2]='/unverified/lean'
  else:raise ValueError(kind)
  put(t,bp,b);rp=clone/'RESULT.json';r=read(rp);r['BUILD_sha256']=sha(bp);put(t,rp,r)
 for kind in ['missing-route','nonzero-route','boolean-route','wrong-command']:struct_case(kind,lambda t,k=kind:build_case(t,k))
 def foreign_dep(t):
  rp=clone/'RESULT.json';r=read(rp);probe=r['dependency_probes'][0];f=clone/'dependencies'/probe['stdout'];t[f]=f.read_bytes();f.write_text('/tmp/unverified-application.olean\n');probe['stdout_sha256']=sha(f);put(t,rp,r)
 struct_case('foreign-object-path',foreign_dep)
 def cstatus(t):
  f=clone/'C-ram/RECEIPT.json';d=read(f);d['rows']=24;put(t,f,d);rp=clone/'RESULT.json';r=read(rp)
  for row in r['C_artifacts']:
   if row['path']=='C-ram/RECEIPT.json':row['sha256']=sha(f)
  put(t,rp,r)
 struct_case('incomplete-C-route-even-rehashed',cstatus)
 def missing_c_artifact(t):
  rp=clone/'RESULT.json';r=read(rp);r['C_artifacts'].pop();put(t,rp,r)
 struct_case('missing-C-artifact-inventory-row',missing_c_artifact)
 def boolean_probe(t):
  rp=clone/'RESULT.json';r=read(rp);r['dependency_probes'][0]['returncode']=False;put(t,rp,r)
 struct_case('boolean-dependency-returncode',boolean_probe)
 for mode in ['', 'O','OO']:cli('restored-complete-copy',mode,True)
 result={'status':'PASS_ACTUAL_READBACK_OPTIMIZATION_AND_MUTATION_CONTROLS','accepted_run_RESULT_sha256':sha(run/'RESULT.json'),'validator_sha256':sha(script),'controller_sha256':sha(__file__),'commands':rows,'only_experiment_owned_copy_mutated':True,'accepted_run_preserved':True};write(out/'RESULT.json',result);print(len(rows),'actual CLI controls PASS')
if __name__=='__main__':main()
