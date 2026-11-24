#!/usr/bin/env python3
"""Additive source freeze above immutable primary454; never imports proof banks."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, posixpath, re
HERE=Path(__file__).resolve().parent; I=HERE.parent; S=I.parent; R=S.parents[1]
def need(ok,msg):
 if not ok: raise ValueError(msg)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def load(name,p):
 spec=importlib.util.spec_from_file_location(name,p); m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();out=a.out.resolve();need(not out.exists(),'fresh capture required')
 reader=load('header_reader',R/'Solutions/RHLimit.v1/scripts/prepare_pi_manifest.py')
 primary_path=I/'corrected/capture/SOURCE_CLOSURE.json';pm=json.loads(primary_path.read_text());baseline={}
 for b in pm['baseline_manifests']:
  need(sha(R/b['path'])==b['sha256'],'foundation manifest drift')
  for row in json.loads((R/b['path']).read_text())['modules']:baseline[row['module']]=row
 for row in pm['modules']:baseline[row['module']]=row
 need(len(baseline)==454,'immutable primary454 required')
 candidates={};roots=[];exclusions=[]
 def add(m,p,root=False):
  p=p.resolve();need(p.is_relative_to(R),'source outside repository');h=sha(p)
  if m in baseline:
   need(h==baseline[m]['sha256'],'frozen primary source drift:'+m);return
  if m in candidates:need(candidates[m]['sha256']==h,'module collision:'+m)
  else:candidates[m]={'module':m,'original_path':str(p.relative_to(R)),'sha256':h}
  if root and m not in roots:roots.append(m)
 for dr in ['box','spectral','ramanujan','octic','moments','goldbach','integration']:
  for p in sorted((S/dr).glob('*.lean')):add(p.stem,p,True)
 for p in sorted((S/'box/supplement').glob('*.lean')):add(p.stem,p,True)
 endpoint=S/'moments/endpoint/SOURCE_ROOTS.json';ep=json.loads(endpoint.read_text())
 need(ep['status']=='FROZEN_ALL128_MATHEMATICAL_SOURCES_PASS_DEV' and len(ep['modules'])==128,'exact endpoint128 freeze required')
 for row in ep['modules']:
  need(sha(R/row['source'])==row['sha256'],'endpoint frozen source drift');add(row['module'],R/row['source'],True)
 # Intentionally excluded historical attempts, evidence probes, and captured copies
 # are enumerated. They are not silently counted as the requested accepted math.
 selected={row['original_path'] for row in candidates.values()}|{row.get('original_path',row.get('path')) for row in baseline.values()}
 for dr in ['box','spectral','ramanujan','octic','moments','goldbach','integration']:
  for p in sorted((S/dr).rglob('*.lean')):
   rel=str(p.relative_to(R))
   if rel not in selected:exclusions.append({'path':rel,'reason':'historical attempt/evidence/captured duplicate; not a current accepted mathematical module'})
 for p in sorted((R/'IEANTN').rglob('*.lean')):
  if p.name!='Challenge.lean':add('.'.join(p.relative_to(R).with_suffix('').parts),p)
 pv=R/'Solutions/RamanujanSourcePV.v1'
 for p in sorted(pv.rglob('*.lean')):add('.'.join(p.relative_to(pv).with_suffix('').parts),p)
 protected=json.loads((I/'PRE_EDIT_BASELINE.json').read_text())['protected_old_IEANTN_files'];final=[];metadata=[]
 import yaml
 for p in sorted((R/'IEANTN/Nodes').glob('*/*/formalization.yaml')):
  if str((p.parent/'Conclusions.lean').relative_to(R)) in protected:continue
  metadata.append({'path':str(p.relative_to(R)),'sha256':sha(p)})
  meta=yaml.safe_load(p.read_text());sol=R/'Solutions'/meta['node']['id']/'Solution.lean'
  m='Public'+meta['node']['family']+meta['node']['version'].upper()
  if sol.exists():add(m,sol,True)
  for c in meta.get('conclusions')or[]:
   js=[j for j in c.get('justifications',[])if j['id']==c['designated']];need(len(js)==1,'justification identity')
   if js[0]['kind']=='lean-noncompliant':final.append(c['challenge'])
   else:need(js[0]['kind']=='literature','unaccounted new proof obligation')
 generic={'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible'}
 ordered=[];done=set(baseline);active=set();resources={};owned=[]
 def visit(m):
  if m in done:return
  need(m in candidates,'unmapped application:'+m);need(m not in active,'cycle:'+m);active.add(m);row=candidates[m];p=R/row['original_path'];local=[];gen=[]
  for dep in reader.header_imports(p.read_text()):
   need('.Challenge' not in dep,'admitted Challenge import')
   if dep in baseline or dep in candidates:visit(dep);local.append(dep)
   else:need(dep.split('.')[0] in generic,'foreign application:'+m+'->'+dep);gen.append(dep)
  active.remove(m);done.add(m)
  for rel in re.findall(r'include_str\s+"([^"\n]+)"',p.read_text()):
   src=(p.parent/rel).resolve();need(src.is_relative_to(R) and src.is_file(),'include payload');runtime=posixpath.normpath(str(Path(m.replace('.','/')).parent/rel));need(not Path(runtime).is_absolute() and '..'not in Path(runtime).parts,'include runtime scope');rr={'path':str(src.relative_to(R)),'relative_runtime_path':runtime,'sha256':sha(src),'consumer_module':m,'include_string':rel}
   if runtime in resources:need(resources[runtime]['sha256']==rr['sha256'],'include collision')
   resources[runtime]=rr
  ordered.append({**row,'application_imports':local,'generic_imports':gen})
  if p.is_relative_to(S):owned.append(m)
 for m in roots:visit(m)
 out.mkdir(parents=True);frozen=out/'frozen-source';frozen.mkdir()
 for row in ordered:
  p=frozen/(row['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/row['original_path']).read_bytes());row['path']=str(p.relative_to(R))
 for rr in resources.values():
  p=frozen/rr['relative_runtime_path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/rr['path']).read_bytes())
 # Independent environment identity selects all theorem constants in owned modules,
 # including private/generated ones; neither source regex nor author counts decide.
 audit_roots=list(dict.fromkeys(pm['roots']+roots))
 audit='import Lean\n'+''.join('import '+m+'\n'for m in audit_roots)+'\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let mods := #['+','.join(json.dumps(m)for m in sorted(owned))+']\n  let allowed := #[`propext, `Classical.choice, `Quot.sound]\n  let mut count := 0\n  for (name, idx) in env.const2ModIdx.toList do\n    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous\n    if !mods.contains modName.toString then continue\n    let some (.thmInfo _) := env.find? name | continue\n    let axs ← collectAxioms name\n    unless axs.all allowed.contains do throwError "Nonstandard proof axiom {name}: {axs}"\n    let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),("axioms",toJson (axs.map Name.toString))]\n    logInfo m!"RH_SUPPLEMENT_THEOREM {row.compress}"\n    count := count + 1\n  unless count > 0 do throwError "Empty supplement audit"\n  logInfo m!"RH_SUPPLEMENT_AUDIT_PASS {count}"\n'
 audit+='\nprivate partial def parameterUses : Lean.Expr → List (String × Bool)\n  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body\n  | .mdata _ body => parameterUses body\n  | _ => []\n\nrun_cmd do\n  let env ← getEnv\n'
 for name in sorted(set(final)):
  audit+='  match env.find? `'+name+' with\n  | some (.thmInfo d) =>\n    let axs ← collectAxioms `'+name+'\n    unless axs.all #[`propext, `Classical.choice, `Quot.sound].contains do throwError "Final root axiom '+name+'"\n    let row := Json.mkObj [("theorem",toJson '+json.dumps(name)+'),("lambda_parameters",toJson ((parameterUses d.value).map fun (n,b) => Json.mkObj [("name",toJson n),("used_in_body",toJson b)]))]\n    logInfo m!"RH_SUPPLEMENT_BODY {row.compress}"\n  | _ => throwError "Missing actual solution '+name+'"\n'
 p=frozen/'FinalSupplementAudit.lean';p.write_text(audit);ordered.append({'module':'FinalSupplementAudit','original_path':None,'path':str(p.relative_to(R)),'sha256':sha(p),'application_imports':audit_roots,'generic_imports':['Lean']})
 manifest={'schema':'RH_OCTIC_SUPPLEMENT_SOURCE_CLOSURE_V1','primary_manifest_sha256':sha(primary_path),'primary_modules':454,'canonical_metadata':metadata,'endpoint_freeze_path':str(endpoint.relative_to(R)),'endpoint_freeze_sha256':sha(endpoint),'selector_sha256':sha(__file__),'modules':ordered,'resources':list(resources.values()),'roots':roots+['FinalSupplementAudit'],'owned_modules':sorted(owned),'final_roots':sorted(set(final)),'excluded_written_sources':exclusions,'selection':'All accepted current flat campaign mathematics, nested Box supplement, all128 frozen endpoint modules, and every new canonical Solution, with recursive core/import closure; historical attempts/evidence/captured duplicates explicitly excluded. No prebuilt application objects or DEV receipts admitted.'}
 (out/'SOURCE_CLOSURE.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({'modules':len(ordered),'owned':len(owned),'final_roots':len(final),'exclusions':len(exclusions)}))
if __name__=='__main__':main()
