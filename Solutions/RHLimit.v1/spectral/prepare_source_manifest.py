#!/usr/bin/env python3
"""Exact final import closure relative to the root's independently cold261 basis."""
from pathlib import Path
import hashlib,json,re,importlib.util
B=Path(__file__).resolve().parent;S=B.parent;N=S.parents[1];OLD=N/'Solutions/RHContinuation.v1'
spec=importlib.util.spec_from_file_location('parent_manifest',S/'scripts/prepare_pi_manifest.py');parent=importlib.util.module_from_spec(spec);spec.loader.exec_module(parent)
need=parent.need;sha=parent.sha;imports=parent.header_imports
BASE=S/'pi/SOURCE_CLOSURE.json';base=json.loads(BASE.read_text());known={r['module']:r for r in base['modules']};candidates={};choices=[]
def add(mod,p,expected=None):
 p=p.resolve();h=sha(p);need(expected is None or expected==h,'pin:'+mod)
 if mod in known:
  if h!=known[mod]['sha256']:
   need(mod=='FullRH','unexpected base identity collision:'+mod)
   choices.append({'module':mod,'selected':known[mod],'unused':{'path':str(p.relative_to(N)),'sha256':h},'reason':'PNTFullRHselectedbycold261; no new consumer calls oldclassical_one/076'})
  return
 if mod in candidates:need(candidates[mod]['sha256']==h,'ambiguous source identity:'+mod);return
 candidates[mod]={'module':mod,'path':str(p.relative_to(N)),'sha256':h}
ram=N/'Solutions/RHExposureStudy.v1/Ramanujan640'
for r in json.loads((ram/'SOURCE_MANIFEST.json').read_text())['modules']:
 add(r['module'],ram/'source'/(r['module'].replace('.','/')+'.lean'),r['source_sha256'])
for p in sorted((OLD/'ramanujan').glob('*.lean')):add(p.stem,p)
for p in sorted((OLD/'ramanujan/source_component').rglob('*.lean')):
 add('.'.join(p.relative_to(OLD/'ramanujan/source_component').with_suffix('').parts),p)
for r in json.loads((OLD/'signed/SOURCE_MANIFEST.json').read_text())['modules']:
 add(r['module'],OLD/'signed'/r['path'],r['sha256'])
for p in sorted(B.glob('*.lean')):add(p.stem,p)
roots=['Ram620Result','BetaDecimal'];done=set(known);active=set();ordered=[];resources=[]
generic={'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible'}
F=B/'frozen-source';F.mkdir(exist_ok=True)
def visit(mod):
 if mod in done:return
 need(mod in candidates,'unmapped application:'+mod);need(mod not in active,'cycle:'+mod);active.add(mod);r=candidates[mod]
 p=N/r['path'];text=p.read_text();names=imports(text);local=[];ext=[]
 for dep in names:
  if dep in known or dep in candidates:visit(dep);local.append(dep)
  else:need(dep.split('.')[0]in generic,'unmapped import:'+mod+'→'+dep);ext.append(dep)
 active.remove(mod);done.add(mod)
 target=F/(mod.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True)
 need(not target.exists()or sha(target)==r['sha256'],'frozen source changed:'+mod)
 target.write_bytes(p.read_bytes())
 for rel in re.findall(r'include_str\s+"([^"\n]+)"',text):
  resource=(p.parent/rel).resolve();dest=(target.parent/rel).resolve()
  need(resource.is_file()and dest.is_relative_to(F),'unmapped/outofscope include:'+mod+':'+rel)
  dest.parent.mkdir(parents=True,exist_ok=True);h=sha(resource)
  need(not dest.exists()or sha(dest)==h,'frozen resource collision');dest.write_bytes(resource.read_bytes())
  resources.append({'path':str(dest.relative_to(N)),'original_path':str(resource.relative_to(N)),'sha256':h})
 ordered.append({**r,'path':str(target.relative_to(N)),'original_path':r['path'],'application_imports':local,'generic_imports':ext})
for mod in roots:visit(mod)
j={'schema':'RH_LIMIT_SPECTRAL_SOURCE_CLOSURE_V1','basis_manifest':str(BASE.relative_to(N)),'basis_manifest_sha256':sha(BASE),'basis_modules':len(known),'roots':roots,'modules':ordered,'resources':resources,'identity_choices':choices,'final_roots':['RHLimit.NicolasMass.mass_lt_047','RHLimit.Ram620.actual_ramanujan_strict620','RHLimit.Ram620.actual_prime_counting_gap620','RHLimit.Ram620.retains_original_margin'],'source_selection':'Exact recursive final-root imports; no oldsorryheuristic; basis261replayedbeforeappend'}
(B/'SOURCE_CLOSURE.json').write_text(json.dumps(j,indent=2)+'\n');print('missing application source modules:',len(ordered),'resources:',len(resources))
