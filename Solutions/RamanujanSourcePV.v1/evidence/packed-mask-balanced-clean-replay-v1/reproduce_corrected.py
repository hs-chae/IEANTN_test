#!/usr/bin/env python3
"""Regenerate exact sources; optionally fresh-rebuild the standalone kernel provider."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys
HERE=Path(__file__).resolve().parent/'original-codec-packet'

def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):
 def pairs(items):
  result={}
  for key,value in items:
   need(key not in result,'duplicate JSON key');result[key]=value
  return result
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--kernel',action='store_true');p.add_argument('--context',type=Path);p.add_argument('--cpus',default='32');p.add_argument('--host-reserve-gib',type=int,default=512);a=p.parse_args()
 out=a.out.resolve();need(not out.exists()and out.parent.is_dir(),'fresh output, existing parent');need(not a.kernel or a.context is not None,'--kernel requires relocated pinned generic --context');out.mkdir()
 flags=[]if sys.flags.optimize==0 else['-'+'O'*sys.flags.optimize]
 command=[sys.executable,*flags,str(HERE/'scripts/generate_balanced_mask_data.py'),'--baseline-source',str(HERE/'inputs/accepted-mask-input.lean.txt'),'--out',str(out/'generated'),'--data-only-4096','--provider-check']
 subprocess.run(command,check=True)
 expected=read(HERE/'REGENERATED_SOURCE_HASHES.json');manifest=read(out/'generated/PROPOSAL.json');records=manifest['records'];need(len(records)==len(expected)==8,'exact generated universe')
 actual={r['module']:sha(r['source'])for r in records};need(actual==expected,'exact accepted regenerated source bytes')
 (out/'REGENERATION.json').write_text(json.dumps(dict(status='EXACT_SOURCE_REGENERATION_PASS',kernel_replay=False,python_optimization=sys.flags.optimize,command=command,sources=actual),indent=2)+'\n')
 if not a.kernel:
  print('EXACT_SOURCE_REGENERATION_PASS; no new Lean replay performed');return
 context=read(a.context);pin=read(HERE/'BUILD_CONTEXT.json');need(context['compiler_sha256']==pin['compiler_sha256'],'same compiler pin');need([(x['name'],x['revision'])for x in context['generic_dependencies']]==[(x['name'],x['revision'])for x in pin['generic_dependencies']],'same generic dependency pins')
 tooling=out/'tooling/project/source';(tooling/'scripts').mkdir(parents=True)
 for name in ['reproduce_profiled_closure.py','rebuild_qrh_closure.py']:shutil.copyfile(HERE/'scripts'/name,tooling/'scripts'/name)
 shutil.copytree(HERE/'source',out/'application-source')
 root='RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.ProviderCheck';prefix='RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.'
 command=[sys.executable,*flags,str(tooling/'scripts/reproduce_profiled_closure.py'),'--context',str(a.context.resolve()),'--out',str(out/'kernel'),'--root',root,'--theorem',prefix+'primitive_program_matches_data','--theorem',prefix+'original_program_matches_data','--application-source-root',str(out/'application-source'),'--application-source-root',str(out/'generated/source'),'--jobs','1','--memory-gib','48','--aggregate-gib','48','--host-reserve-gib',str(a.host_reserve_gib),'--cpus',a.cpus]
 subprocess.run(command,check=True)
 subprocess.run([sys.executable,*flags,str(tooling/'scripts/reproduce_profiled_closure.py'),'--check',str(out/'kernel')],check=True)
 print('Fresh application-source kernel replay accepted; see kernel/RESULT.json')
if __name__=='__main__':main()
