#!/usr/bin/env python3
"""Actual normal/-O/-OO CLIs for the cold-bank analytic append and fail-closed mutations."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys
B=Path(__file__).resolve().parent

def need(b,m):
 if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--base-run',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh controls required');out.mkdir(parents=True);(out/'controls.executed.py').write_bytes(Path(__file__).read_bytes());rows=[];env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
 for flags in ([],['-O'],['-OO']):
  mode='normal'if not flags else flags[0][1:];owned=out/mode;owned.mkdir()
  def cli(name,script,args,ok,expected_text='',child_env=None):
   dest=Path(args[args.index('--out')+1]);receipt=dest/'RESULT.json';before=receipt.read_bytes()if receipt.exists()else None
   cmd=[sys.executable,*flags,str(B/script),*args];r=subprocess.run(cmd,text=True,capture_output=True,env=child_env or env)
   (owned/(name+'.stdout')).write_text(r.stdout);(owned/(name+'.stderr')).write_text(r.stderr)
   need((r.returncode==0)==ok,'acceptance differs:'+mode+':'+name)
   if expected_text:need(expected_text in r.stdout+r.stderr,'wrong rejection/route:'+name)
   if not ok:need(before==(receipt.read_bytes()if receipt.exists()else None),'negative CLI changed final receipt')
   rows.append({'mode':mode,'test':name,'command':cmd,'returncode':r.returncode,'expected_acceptance':ok})
  cli('common-preflight','reproduce_common.py',['--out',str(owned/'common-noout'),'--check'],True,'PASS_COMMON_SOURCE_PREFLIGHT_ONLY')
  cli('absolute-preflight','reproduce_absolute.py',['--out',str(owned/'absolute-noout'),'--check'],True,'PASS_ABSOLUTE_SOURCE_PREFLIGHT_ONLY')
  cli('actual-source-proof-append','reproduce_absolute.py',['--out',str(owned/'accepted'),'--base-run',str(a.base_run)],True,'PASS_SOURCE_LINKED_ACTUAL_OCTIC_ABSOLUTE_STIELTJES')
  cli('existing-output','reproduce_absolute.py',['--out',str(owned/'accepted'),'--check'],False,'fresh output required')
  for name,raw in [('duplicate-context','{"compiler_sha256":"x","compiler_sha256":"y"}'),('nonfinite-context','{"bad":1e999}')]:
   f=owned/(name+'.json');f.write_text(raw);e=env.copy();e['IEANTN_GENERIC_CONTEXT']=str(f)
   cli(name,'reproduce_absolute.py',['--out',str(owned/(name+'-out')),'--check'],False,'duplicate JSON key'if name.startswith('duplicate')else'nonfinite JSON',e)
  fake=owned/'mutated-bank';fake.mkdir()
  for name in ['RESULT.json','BUILD.json','reproduce.executed.py']:shutil.copyfile(a.base_run/name,fake/name)
  shutil.copytree(a.base_run/'source',fake/'source');shutil.copytree(a.base_run/'objects',fake/'objects')
  q=fake/'objects/EvenKernel.olean';raw=q.read_bytes();q.write_bytes(raw+b'OWNED_CONTROL_CORRUPTION')
  cli('changed-object','reproduce_absolute.py',['--out',str(owned/'bad-object-out'),'--base-run',str(fake)],False,'base source/object bytes');q.write_bytes(raw)
  q=fake/'source/BPTZeroCount.lean';raw=q.read_bytes();q.write_bytes(raw+b'\n-- OWNED_CONTROL_CORRUPTION\n')
  cli('changed-source','reproduce_absolute.py',['--out',str(owned/'bad-source-out'),'--base-run',str(fake)],False,'base source/object bytes')
  files=[{'path':str(f.relative_to(fake)),'sha256':sha(f),'bytes':f.stat().st_size}for f in sorted(fake.rglob('*'))if f.is_file()]
  need(fake.resolve().is_relative_to(out)and not fake.is_symlink(),'cleanup ownership')
  for row in files:
   f=fake/row['path'];need(f.is_file()and not f.is_symlink()and sha(f)==row['sha256'],'cleanup preview changed')
  for row in files:(fake/row['path']).unlink()
  for d in sorted([x for x in fake.rglob('*')if x.is_dir()],key=lambda x:len(x.parts),reverse=True):d.rmdir()
  fake.rmdir();(owned/'MUTATED_BANK_CLEANUP.json').write_text(json.dumps({'status':'REMOVED_VERIFIED_REGENERABLE_REDUNDANT_CONTROL_COPIES','base_preserved':str(a.base_run),'bytes_removed':sum(x['bytes']for x in files),'files':files,'regeneration':'This controls script copies retained original bank, applies the exact deterministic byte mutations, executes both rejection tests, then verifies/removes only its own redundant copies.'},indent=2)+'\n')
 receipt={'status':'PASS_ALL_MODE_COMMON_ABSOLUTE_CLI_CONTROLS','controller_sha256':sha(__file__),'common_validator_sha256':sha(B/'reproduce_common.py'),'absolute_validator_sha256':sha(B/'reproduce_absolute.py'),'base_result_sha256':sha(a.base_run/'RESULT.json'),'rows':rows,'fresh_source_graph':'Separate actual cold113-v2 receipt; this control executes all common/absolute preflights and actual source-proof append in every Python optimization mode, plus byte/source/context rejection controls.'};q=out/'.RESULT.pending';q.write_text(json.dumps(receipt,indent=2)+'\n');q.replace(out/'RESULT.json');print(receipt['status'])
if __name__=='__main__':main()
