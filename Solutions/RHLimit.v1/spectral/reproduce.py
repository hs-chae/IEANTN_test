#!/usr/bin/env python3
"""Replay spectral/Ram620 source against an explicitly supplied application foundation.

This runner compiles every new source and checks all printed dependency roots.
The root study's clean source replay supplies the foundation; this is not a
substitute for proving or freshly replaying its imported application sources.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,time
B=Path(__file__).resolve().parent
ORDER=['SpectralGMRefined','NicolasSpectralMass','BetaDecimal','Ram620Low','Ram620Anchors',
       'Ram620Powers','Ram620Bands','Ram620Finite','Ram620Leaves','Ram620Result']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False)
 p.add_argument('--out',type=Path,required=True)
 p.add_argument('--foundation-library',type=Path,action='append',required=True,
  help='Application libraries already freshly replayed by the complete study controller; include NicolasBaseline for mass track.')
 a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh output required')
 out.mkdir(parents=True);started=time.monotonic()
 # Regenerate numerical scout and exact Lean goal text; reject any drift.
 scout=subprocess.run([sys.executable,str(B/'scout_620_bridge.py')],capture_output=True,text=True,check=True)
 (out/'NUMERICAL_DISCOVERY.json').write_text(scout.stdout)
 before=sha(B/'Ram620Leaves.lean')
 subprocess.run([sys.executable,str(B/'generate_620_leaves.py')],check=True)
 need(sha(B/'Ram620Leaves.lean')==before,'generated exact proof goals drifted')
 proofs=[];records=[]
 for module in ORDER:
  dest=out/module
  cmd=[sys.executable,str(B/'compile_development.py'),'--module',module,'--out',str(dest)]
  for lib in a.foundation_library:cmd+=['--foundation-library',str(lib.resolve())]
  for lib in proofs:cmd+=['--extra-library',str(lib)]
  cp=subprocess.run(cmd,capture_output=True,text=True)
  (out/(module+'.driver.stdout')).write_text(cp.stdout)
  (out/(module+'.driver.stderr')).write_text(cp.stderr)
  need(cp.returncode==0,'proof compilation failed: '+module)
  r=json.loads((dest/'RESULT.json').read_text());need(r['status']=='PASS','nonpass proof: '+module)
  r['module']=module;r['object_sha256']=sha(dest/'objects'/(module+'.olean'))
  records.append(r);proofs.append(dest/'objects')
 result={'schema':'RH_LIMIT_SPECTRAL_REPLAY_V1','status':'PASS_NEW_SOURCE_AND_ACTUAL_CONSUMERS',
  'source_first_PV':False,'new_numerical_verification':'kernel-only',
  'foundation_policy':'Complete study controller supplies its own fresh application source closure; this runner only proves the new modules.',
  'elapsed_seconds':time.monotonic()-started,'modules':records}
 (out/'REPLAY.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':result['status'],'elapsed_seconds':result['elapsed_seconds']}))
if __name__=='__main__':main()
