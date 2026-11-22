#!/usr/bin/env python3
"""Select exact import closure for the actual ordinary-pi theorem roots."""
from pathlib import Path
import hashlib,json,re
S=Path(__file__).resolve().parents[1];N=S.parents[1];OLD=N/'Solutions/RHContinuation.v1'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_bytes())
def header_imports(text):
 # Lean imports occur in the header. Stop before declarations or quotations.
 i=0;imports=[]
 while i<len(text):
  while i<len(text)and text[i].isspace():i+=1
  if text.startswith('--',i):
   k=text.find('\n',i);i=len(text)if k<0 else k+1;continue
  if text.startswith('/-',i):
   depth=1;i+=2
   while depth and i<len(text):
    if text.startswith('/-',i):depth+=1;i+=2
    elif text.startswith('-/',i):depth-=1;i+=2
    else:i+=1
   need(depth==0,'unterminated header comment');continue
  k=text.find('\n',i);k=len(text)if k<0 else k
  line=text[i:k].split('--',1)[0].strip()
  if line=='prelude':i=k+1;continue
  m=re.fullmatch(r'(?:(?:public|private)\s+)?import\s+([A-Za-z0-9_.\s]+)',line)
  if not m:break
  imports.extend(m.group(1).split());i=k+1
 return imports

def main():
 candidates={};exceptions=[]
 def add(mod,path,expected=None,priority=False):
  path=path.resolve();h=sha(path);need(expected is None or expected==h,'source pin:'+mod)
  if mod in candidates and candidates[mod]['sha256']!=h:
   if mod=='FullRH':
    exceptions.append({'module':mod,'selected':candidates[mod],'unused_variant':{'path':str(path.relative_to(N)),'sha256':h},'reason':'PNT and Ram archives differ only in their unused classical_one/classical_076 declarations. The PNT source is selected and every consumer is recompiled in one coherent module environment.'});return
   raise ValueError('unresolved source identity collision:'+mod)
  candidates[mod]={'module':mod,'path':str(path.relative_to(N)),'sha256':h}
 # PNT named-source selection takes precedence over the historical Ram variant.
 for r in read(OLD/'integration/SOURCE_CLOSURE.json')['modules']:add(r['module'],OLD/'integration'/r['frozen'],r['sha256'])
 ram=N/'Solutions/RHExposureStudy.v1/Ramanujan640'
 for r in read(ram/'SOURCE_MANIFEST.json')['modules']:
  add(r['module'],ram/'source'/(r['module'].replace('.','/')+'.lean'),r['source_sha256'])
 for r in read(OLD/'parabolic/evidence/clog-final-current-v2/SOURCE_CLOSURE.json'):
  add(r['module'],Path(r['source']),r['sha256'])
 plan=read(S/'scripts/PI_SOURCE_HELPERS.json')
 for r in plan['modules']:add(r['module'],N/r['source'],r['sha256'])
 for folder in ['pi','analytic']:
  for p in sorted((S/folder).glob('*.lean')):add(p.stem,p)
 roots=['PurePiRay','SourceBoxPi'];ordered=[];active=set();done=set()
 generic={'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible'}
 def visit(mod):
  if mod in done:return
  need(mod not in active,'cyclic imports:'+mod);active.add(mod);r=candidates[mod]
  imports=header_imports((N/r['path']).read_text())
  local=[];ext=[]
  for name in imports:
   if name in candidates:visit(name);local.append(name)
   else:need(name.split('.')[0]in generic,'unmapped application import:'+mod+' → '+name);ext.append(name)
  active.remove(mod);done.add(mod);ordered.append({**r,'application_imports':local,'generic_imports':ext})
 for mod in roots:visit(mod)
 j={'schema':'RH_LIMIT_ACTUAL_PI_SOURCE_CLOSURE_V1','roots':roots,'source_selection':'Exact recursive imports of the final actual ordinary-pi and source-linked box consumers, not a historical sorry queue.','module_identity_choices':exceptions,'modules':ordered,'no_prebuilt_application_or_LeanCert_objects':True,'final_roots':['RHLimit.PurePi.ch_pi_stronger_classical','RHLimit.PurePi.ch_at_100','RHLimit.PurePi.box_at_100','RHLimit.PurePi.source_box_Epi','RHLimit.PurePi.source_box_Epi_at_100'],'source_first_PV_scope':'Reused actual finite-log C source→AST→execution→127-word bounds→moment→box psi→ordinary pi. New analysis and kernel-only scalar enclosures are not PV.'}
 (S/'pi/SOURCE_CLOSURE.json').write_text(json.dumps(j,indent=2)+'\n');print('selected',len(ordered),'modules; identity choices',len(exceptions))
if __name__=='__main__':main()
