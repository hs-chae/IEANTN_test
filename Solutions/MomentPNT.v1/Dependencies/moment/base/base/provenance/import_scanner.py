#!/usr/bin/env python3
"""Source-only current43 snapshot; no Lean process or fresh acceptance claim."""
from pathlib import Path
import hashlib,json,re
B=Path(__file__).resolve().parent;R=B.parents[1]
def need(v,m):
 if not v:raise RuntimeError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def resolve(raw):
 p=Path(raw);return p if p.is_absolute()else R/p

def imports(text):
 # Preserve newlines while removing nested comments and string contents, so
 # documentation/code strings cannot masquerade as import commands.
 result=[];i=0;depth=0;quoted=False
 while i<len(text):
  c=text[i];pair=text[i:i+2]
  if depth:
   if pair=='/-':depth+=1;i+=2;continue
   if pair=='-/':depth-=1;i+=2;continue
   result.append('\n'if c=='\n'else' ');i+=1;continue
  if quoted:
   if c=='\\':result.extend('  ');i+=2;continue
   if c=='"':quoted=False
   result.append('\n'if c=='\n'else' ');i+=1;continue
  if pair=='/-':depth=1;i+=2;continue
  if pair=='--':
   end=text.find('\n',i);i=len(text)if end<0 else end;continue
  if c=='"':quoted=True;result.append(' ');i+=1;continue
  result.append(c);i+=1
 clean=''.join(result);need(depth==0,'unclosed source comment')
 out=[]
 for line in clean.splitlines():
  line=line.strip()
  if line.startswith('import ')or line.startswith('public import '):
   tail=line.split('import ',1)[1].strip();names=tail.split()
   need(bool(names)and all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',x)for x in names),'unsupported import header '+line)
   out.extend(names)
 return list(dict.fromkeys(out))

def main():
 e=json.loads((R/'scoped/build/DEVELOPMENT_ENVIRONMENT.json').read_text())
 old_manifest=json.loads((R/'scoped/evaluate-source-v1/DEPENDENCY_SOURCE_MANIFEST_V1.json').read_text())
 baseline_manifest=json.loads((R/'scoped/body-replay/DEPENDENCY_SOURCE_MANIFEST_V3.json').read_text())
 baselock=json.loads((R/'scoped/body-replay/capsule-v3/SOURCE_LOCK.json').read_text())
 numerical=json.loads((R/'scoped/frontend/proof/SOURCE_HELPER_SUPPORT_INDEX_V13.json').read_text())
 control=json.loads((R/'scoped/evaluate-source-v1/CURRENT_CONTROLS_BODY_AND_MATH_INDEX_V3.json').read_text())
 own=json.loads((R/'scoped/evaluate-source-v1/SOURCE_SUPPORT_INDEX_V1.json').read_text())
 need(control['aggregate_actual_whole_bodies']==43,'fixed forty-three-body population')
 evidence={};records={};roots={};root_modules=[]
 def add_receipt(raw):
  p=resolve(raw);j=json.loads(p.read_text());need(j.get('exit_code')==0 and j.get('source_unchanged'),'accepted host proof '+str(p));src=resolve(j['source']);need(sha(src)==j['source_sha256'],'current source/receipt '+str(src))
  audit=j.get('audit',[]);need(all(set(x['axioms'])<={'propext','Classical.choice','Quot.sound'}for x in audit),'selected Std3 audit '+str(p))
  module=j['module'];records[module]=dict(module=module,source=str(src),source_sha256=sha(src),receipt=str(p),receipt_sha256=sha(p),audits=[dict(name=x['name'],axioms=x['axioms'])for x in audit])
  evidence[str(p)]=dict(path=str(p),sha256=sha(p),kind='accepted individual host compile')
  for x in audit:roots[x['name']]=x['axioms']
  if module not in root_modules:root_modules.append(module)
 for row in numerical['files']:
  need(sha(resolve(row['source']))==row['source_sha256']and sha(resolve(row['receipt']))==row['receipt_sha256'],'numerics index drift '+row['module']);add_receipt(row['receipt'])
 for row in own['records']:add_receipt(row['receipt'])
 for row in control['new_controls_exact_output_records']:add_receipt(row['receipt'])
 extra=['FloorQFrames','SourceFloorQNonnegative','SourceFloorQNonnegativeMath','FloorQNegativeFrames','FloorQNegativeCalls','CallEventNames','SourceFloorQIntegral','FloorQIncrementCalls','SourceFloorQNonintegral','SourceFloorQAll','SourceFloorQBudget','SourceCeilData','SourceCeilQ','SourceFloorQFraming','SourceCeilQFraming','CursorSingleFrames','SourceFloorQTrace','LocalBinding','FromRIFrames','SourceCeilQTrace','FromRIFactor','RationalMultiplyTrace','SourceRoundProduct','FromRIStages','FromRIMemory','CallEventKeys','FromRIExpressions','FromRIServices','FromRIOutput','SourceFromRI','NumericFromRIRefinement','SourceFromRIArguments','SourceIconst']
 accepted={}
 for p in (R/'scoped/frontend/proof').rglob('RECEIPT.json'):
  if p.stat().st_size>30000000:continue
  try:j=json.loads(p.read_text())
  except (ValueError,OSError):continue
  if j.get('status')!='PASS_HOST_DEVELOPMENT_COMPILE':continue
  module=j.get('module','');name=module.removeprefix('ScopedC.')
  if name not in extra:continue
  src=resolve(j['source'])
  if src.is_file()and sha(src)==j['source_sha256']:accepted[name]=p
 need(set(extra)<=set(accepted),'missing current accepted supplement '+str(set(extra)-set(accepted)))
 for name in extra:add_receipt(accepted[name])
 # Preserve the old independently replayed17-body evidence and all its roots.
 cold=R/'scoped/build/merged-body28-c56-cold-v3/RECEIPT.json';cj=json.loads(cold.read_text());need(cj['status'].startswith('PASS_'),'old full source-cold evidence')
 evidence[str(cold)]=dict(path=str(cold),sha256=sha(cold),kind='preserved older343-source60-root cold replay; not a current43 replay')
 for name in baselock['roots']:roots.setdefault(name,[])
 for name in baselock['root_modules']:
  if name not in root_modules:root_modules.append(name)
 own_roots=[R/'network',R/'scoped/stdio-v1/lean',R/'scoped/checked-io-v1/lean',R/'scoped/auxiliary/lean',R/'scoped/frontend/lean',R/'scoped/numerical/lean',R/'scoped/input-data/lean',R/'scoped/source-bundle/lean',R/'scoped/source-bundle/capsule-v1/lean']
 previous={}
 for m in [baseline_manifest,old_manifest]:
  for row in m['source_records']:previous[row['module']]=row
 assoc=json.loads((R/'scoped/build/DEVELOPMENT_OBJECT_ASSOCIATION.json').read_text())['rows'];fallback={x['module']:x for x in assoc if x.get('source')}
 generic=[Path(d['objects'])for d in e['generic_dependencies']]+[Path(e['compiler']).parent.parent/'lib/lean']
 seen={};order=[];generic_imports=set();cached_comparisons=[]
 def source(module):
  rel=Path(module.replace('.','/')).with_suffix('.lean')
  for root in own_roots:
   p=root/rel
   if p.is_file():return p
  if module in previous:
   row=previous[module];p=Path(row['source']);need(p.is_file()and sha(p)==row['sha256'],'old source association '+module);return p
  if module in fallback:
   row=fallback[module];p=Path(row['source']);need(p.is_file()and sha(p)==row['source_sha256'],'baseline source association '+module);return p
  raise RuntimeError('missing application source '+module)
 def is_generic(module):
  rel=Path(module.replace('.','/')).with_suffix('.olean');return any((g/rel).is_file()for g in generic)
 def visit(module):
  if module in seen:need(seen[module]is not None,'source import cycle '+module);return
  p=source(module);h=sha(p);seen[module]=None;deps=[]
  for child in imports(p.read_text()):
   if is_generic(child):generic_imports.add(child);continue
   deps.append(child);visit(child)
  if module in previous and previous[module]['sha256']==h:
   need(set(previous[module]['imports'])==set(deps),'strict header differs from prior actual compiler import closure '+module)
   cached_comparisons.append(module)
  seen[module]=dict(module=module,source=str(p),sha256=h,bytes=p.stat().st_size,imports=deps);order.append(module)
 for module in root_modules:visit(module)
 support=dict(status='SOURCE_ONLY_CURRENT43_ACCEPTED_COMPONENT_SNAPSHOT_NO_NEW_COLD_REPLAY',records=list(records.values()),root_modules=root_modules,roots=list(roots),accepted_host_modules=len(records),current_whole_body_count=43,evidence=list(evidence.values()),numerics_index_sha256=sha(R/'scoped/frontend/proof/SOURCE_HELPER_SUPPORT_INDEX_V13.json'),controls_index_sha256=sha(R/'scoped/evaluate-source-v1/CURRENT_CONTROLS_BODY_AND_MATH_INDEX_V3.json'),qualification='Selected exact current accepted source/math roots plus preserved older343 cold evidence. This current43 closure has not been freshly replayed. New ArrayLegacyLift is separate. Source prepare/evaluate/main/I/O/output-to-ANT chain remains incomplete.')
 manifest=dict(status='SOURCE_ONLY_STRICT_HEADER_CLOSURE_WITH_PREVIOUS_COMPILER_CLOSURE_CROSSCHECKS',compiler_sha256=sha(Path(e['compiler'])),source_records=[seen[x]for x in order],topological_modules=order,root_modules=root_modules,generic_dependency_pins=[{k:v for k,v in x.items()if k in ['name','url','commit']}for x in e['generic_dependencies']],generic_imports=sorted(generic_imports),matching_previous_actual_compiler_import_rows=len(cached_comparisons),new_Lean_deps_queries_executed=False,qualification='No Lean/compiler process is launched by this snapshot generator. Strict import-header parsing was checked against prior actual compiler closures for unchanged sources; new source headers are not separately compiler-queried. The included generic-only clean rebuild is the acceptance gate, not this source snapshot.')
 (B/'SOURCE_SUPPORT_INDEX_V1.json').write_text(json.dumps(support,indent=2)+'\n');(B/'DEPENDENCY_SOURCE_MANIFEST_V1.json').write_text(json.dumps(manifest,indent=2)+'\n')
 print(json.dumps(dict(application_sources=len(order),accepted_host_modules=len(records),roots=len(roots),whole_bodies=43,previous_compiler_rows_compared=len(cached_comparisons),fresh_cold_replay=False)))
if __name__=='__main__':main()
