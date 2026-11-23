#!/usr/bin/env python3
"""Capture the exact canonical+entire-profile application extension of cold316."""
from pathlib import Path
import hashlib,json,importlib.util
S=Path(__file__).resolve().parents[1];N=S.parents[1]
spec=importlib.util.spec_from_file_location('selector',S/'scripts/prepare_pi_manifest.py');u=importlib.util.module_from_spec(spec);spec.loader.exec_module(u)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,msg):
 if not ok:raise ValueError(msg)
def main():
 base=json.loads((S/'pi/SOURCE_CLOSURE.json').read_text());ext=json.loads((S/'spectral/SOURCE_CLOSURE.json').read_text());done={r['module']for r in base['modules']+ext['modules']};candidates={}
 def add(mod,p):
  if mod in done:return
  p=p.resolve();r={'module':mod,'path':str(p.relative_to(N)),'sha256':sha(p)}
  need(mod not in candidates or candidates[mod]['sha256']==r['sha256'],'module identity collision:'+mod);candidates[mod]=r
 for d in ['octic','analytic']:
  for p in (S/d).glob('*.lean'):add(p.stem,p)
 for p in (N/'Solutions/RHContinuation.v1/ramanujan').glob('*.lean'):add(p.stem,p)
 for rel in ['IEANTN/Nodes/RHPrimeCounting/v1/Conclusions.lean','IEANTN/Nodes/RHPrimeCounting/v2/Conclusions.lean','IEANTN/Nodes/PrimeKernelInputs/v2/Conclusions.lean','IEANTN/Nodes/RamanujanGap/v3/Conclusions.lean','IEANTN/Nodes/RamanujanGap/v4/Conclusions.lean']:
  add(rel[:-5].replace('/','.'),N/rel)
 aliases={'LimitPiSolution':'Solutions/RHPrimeCounting.v2/Solution.lean','LimitKernelSolution':'Solutions/PrimeKernelInputs.v1/Solution.lean','LimitMellinSolution':'Solutions/BoxMellinInputs.v1/Solution.lean','LimitRamSolution':'Solutions/RamanujanGap.v4/Solution.lean','OldRamFullSolution':'Solutions/RamanujanGap.v3/Solution.lean','NetworkEvolution':'Solutions/RHLimit.v1/integration/NetworkEvolution.lean'}
 for mod,path in aliases.items():add(mod,N/path)
 ordered=[];active=set()
 def visit(mod):
  if mod in done:return
  need(mod not in active,'cyclic import:'+mod);active.add(mod)
  r=candidates[mod];imports=u.header_imports((N/r['path']).read_text());local=[];generic=[]
  for name in imports:
   if name in candidates or name in done:visit(name);local.append(name)
   else:need(name.split('.')[0]in {'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible'},'unmapped application:'+mod+'→'+name);generic.append(name)
  active.remove(mod);done.add(mod);ordered.append({**r,'application_imports':local,'generic_imports':generic})
 for name in ['NetworkEvolution','OcticStrict','AbsoluteStieltjes']:visit(name)
 for r in ordered:
  if not r['path'].startswith('Solutions/RHLimit.v1/'):
   r['original_path']=r['path'];f=N/r['path'];q=S/'integration/frozen-source'/(r['module'].replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(f.read_bytes());r['path']=str(q.relative_to(N))
 m={'schema':'RH_LIMIT_FINAL_CANONICAL_EXTENSION_V1','basis_modules':316,'basis_manifests':[{'path':'Solutions/RHLimit.v1/pi/SOURCE_CLOSURE.json','sha256':sha(S/'pi/SOURCE_CLOSURE.json')},{'path':'Solutions/RHLimit.v1/spectral/SOURCE_CLOSURE.json','sha256':sha(S/'spectral/SOURCE_CLOSURE.json')}],'modules':ordered,'roots':['NetworkEvolution','OcticStrict','AbsoluteStieltjes'],'final_roots':['RHLimit.Network.octic_forward_evolution','RHLimit.Network.box_forward_evolution','RHLimit.Network.ramanujan_full_source_evolution'],'generated_Challenge_scaffolds_imported':False}
 (S/'integration/SOURCE_CLOSURE.json').write_text(json.dumps(m,indent=2)+'\n');print('canonicalextension',len(ordered),'total',316+len(ordered))
if __name__=='__main__':main()
