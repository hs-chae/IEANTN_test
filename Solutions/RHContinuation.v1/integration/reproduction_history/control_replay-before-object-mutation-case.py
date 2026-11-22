#!/usr/bin/env python3
"""Actual normal/-O/-OO CLI controls on fresh owned fixtures."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time
HERE=Path(__file__).resolve().parent

def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--base-run',type=Path,required=True);a=p.parse_args();O=a.out.resolve();need(not O.exists(),'fresh controls output required');O.mkdir(parents=True);helper=HERE.parent/'scripts/build_modules.py';reference=HERE.parent/'scripts/GENERIC_CONTEXT.json';ctx=json.loads(reference.read_text());start=time.monotonic();runs=[]
 for mode,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
  M=O/mode;M.mkdir();source=M/'tiny-source';source.mkdir();(source/'Smoke.lean').write_text('import Mathlib.Data.Nat.Basic\ntheorem smoke (n : Nat) : n = n := rfl\n#print axioms smoke\n');existing=M/'exists';existing.mkdir()
  def invoke(label,args,positive=False,env=None):
   command=[sys.executable,*flags,*map(str,args)];r=subprocess.run(command,text=True,capture_output=True,env=env);(M/(label+'.stdout')).write_text(r.stdout);(M/(label+'.stderr')).write_text(r.stderr);need((r.returncode==0)==positive,'actual CLI acceptance mismatch:'+mode+':'+label);runs.append({'mode':mode,'case':label,'command':command,'returncode':r.returncode,'expected_success':positive})
  def cmd(out='bad'):
   return[helper,'--source',source,'--out',M/out,'--module','Smoke']
  invoke('positive-helper',cmd('positive'),True)
  badctx=M/'duplicate.json';raw=reference.read_text();badctx.write_text('{"compiler_sha256":"duplicate",'+raw.lstrip()[1:]);env=os.environ.copy();env['IEANTN_GENERIC_CONTEXT']=str(badctx);invoke('duplicate-json',cmd('dup'),env=env)
  nonfinite=M/'nonfinite.json';nonfinite.write_text(raw[:-2]+',"unused":NaN}\n');env2=os.environ.copy();env2['IEANTN_GENERIC_CONTEXT']=str(nonfinite);invoke('nonfinite-json',cmd('nan'),env=env2)
  for label,key,value in [('compiler-pin','compiler_sha256','0'*64),('dependency-pin',None,None)]:
   c=json.loads(raw)
   if key:c[key]=value
   else:c['generic_dependencies'][0]['revision']='0'*40
   f=M/(label+'.json');f.write_text(json.dumps(c));e=os.environ.copy();e['IEANTN_GENERIC_CONTEXT']=str(f);invoke(label,cmd(label+'-out'),env=e)
  invoke('missing-args',[helper]);invoke('zero-modules',[helper,'--source',source,'--out',M/'zero']);invoke('duplicate-modules',cmd('duplicates')+['--module','Smoke']);invoke('unknown-option',cmd('unknown')+['--unknown']);invoke('existing-output',cmd('exists'));invoke('missing-source',[helper,'--source',source,'--out',M/'missing','--module','Missing']);invoke('missing-library',cmd('lib')+['--extra-library',M/'absent'])
  # A genuine incorrect Lean proposition must fail, not merely an argument guard.
  (source/'Wrong.lean').write_text('import Mathlib.Data.Nat.Basic\nexample : False := by decide\n');invoke('invalid-Lean',[helper,'--source',source,'--out',M/'wrong','--module','Wrong'])
  fixture=M/'fixture/network';app=fixture/'Solutions/RHContinuation.v1';dest=app/'integration';dest.mkdir(parents=True);(fixture/'IEANTN/Nodes').mkdir(parents=True);shutil.copytree(HERE.parent/'scripts',app/'scripts',ignore=shutil.ignore_patterns('__pycache__'))
  for name in ['reproduce.py','reproduce_public.py','SOURCE_CLOSURE.json','PUBLIC_SOLUTIONS.json']:shutil.copyfile(HERE/name,dest/name)
  shutil.copytree(HERE/'frozen-source',dest/'frozen-source')
  public=json.loads((dest/'PUBLIC_SOLUTIONS.json').read_text())
  for row in public['files']:
   p=fixture/row['path'];p.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(HERE.parents[2]/row['path'],p)
  invoke('positive-relocated-public',[dest/'reproduce_public.py','--out',M/'relocated-good','--base-run',a.base_run],True)
  # Alter only owned scientific source, keep every original accepted file unchanged.
  first=json.loads((dest/'SOURCE_CLOSURE.json').read_text())['modules'][0];f=dest/first['frozen'];f.write_text(f.read_text()+'\n-- owned mutation\n');invoke('changed-frozen-source',[dest/'reproduce.py','--out',M/'bad-source'])
  # The canonical file identity is independently preflighted before building anything.
  row=public['files'][0];(fixture/row['path']).write_text('theorem different : True := True.intro\n');invoke('changed-canonical',[dest/'reproduce_public.py','--out',M/'bad-public','--base-run',a.base_run])
  invoke('public-missing-args',[dest/'reproduce_public.py']);invoke('public-unknown-option',[dest/'reproduce_public.py','--out',M/'unknown-public','--unknown']);invoke('public-existing-output',[dest/'reproduce_public.py','--out',M/'relocated-good','--base-run',a.base_run])
 result={'status':'PASS_ACTUAL_CLI_CONTROLS_ALL_OPTIMIZATION_MODES','seconds':time.monotonic()-start,'cases':runs,'actual_child_invocations':len(runs),'positive_cases':sum(x['expected_success']for x in runs),'negative_cases':sum(not x['expected_success']for x in runs),'helper_sha256':sha(helper),'reproducer_sha256':sha(HERE/'reproduce.py'),'public_reproducer_sha256':sha(HERE/'reproduce_public.py'),'control_validator_sha256':sha(__file__),'assert_used_for_acceptance':False};temp=O/'RESULT.pending';temp.write_text(json.dumps(result,indent=2)+'\n');os.replace(temp,O/'RESULT.json');print(json.dumps({'status':result['status'],'cases':len(runs),'seconds':result['seconds']}))
if __name__=='__main__':main()
