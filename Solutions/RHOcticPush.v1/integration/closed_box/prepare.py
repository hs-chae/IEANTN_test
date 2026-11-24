#!/usr/bin/env python3
"""Freeze exact completed Box sources and their actual final canonical consumers."""
from pathlib import Path
import hashlib,json,importlib.util,re,yaml
H=Path(__file__).resolve().parent;I=H.parent;S=I.parent;R=S.parents[1]
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def load(n,p):
 s=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
reader=load('header_parser',R/'Solutions/RHLimit.v1/scripts/prepare_pi_manifest.py')
basis={}
pm=read(I/'corrected/capture/SOURCE_CLOSURE.json')
for q in pm['baseline_manifests']:
 for x in read(R/q['path'])['modules']:basis[x['module']]=x
for m in [pm,read(I/'supplement/audit-corrected-capture/SOURCE_CLOSURE.json'),read(S/'box/zero/cold-capture/SOURCE_CLOSURE.json')]:
 for x in m['modules']:need(x['module']not in basis,'basis collision');basis[x['module']]=x
need(len(basis)==660,'exact sourcefresh660 foundation')
freeze=S/'box/perron/SOURCE_FREEZE.json';f=read(freeze);need(len(f['modules'])==15,'all15 Perron science')
candidates={};owned=[]
def add(mod,p,own=False):
 p=Path(p);need(p.is_file(),'source missing:'+str(p));need(mod not in basis and mod not in candidates,'source collision:'+mod);candidates[mod]={'module':mod,'original_path':str(p.relative_to(R)),'sha256':sha(p)}
 if own:owned.append(mod)
for q in f['modules']:
 p=R/q['source'];need(sha(p)==q['sha256'],'accepted Perron source drift');rc=read(R/q['receipt']);need(rc['status']=='PASS_DEV' and type(rc['returncode'])is int and rc['returncode']==0 and rc['source_sha256']==q['sha256'],'actual accepted Perron receipt');add(q['module'],p,True)
versions=[('BoxMellinInputs','v2'),('IntegratedPerron','v1'),('RHSmoothingInputs','v2'),('RHSmoothing','v3'),('Lcm','v6'),('RHPrimeCounting','v4'),('Primorial','v4')];metadata=[];final=[];lit=[]
for family,version in versions:
 d=R/'IEANTN/Nodes'/family/version;add('IEANTN.Nodes.'+family+'.'+version+'.Conclusions',d/'Conclusions.lean');meta=yaml.safe_load((d/'formalization.yaml').read_text());metadata.append({'path':str((d/'formalization.yaml').relative_to(R)),'sha256':sha(d/'formalization.yaml')})
 for c in meta['conclusions']:
  js=[j for j in c['justifications']if j['id']==c['designated']];need(len(js)==1,'designated identity')
  if js[0]['kind']=='literature':lit.append(c['declaration'])
  else:need(js[0]['kind']=='lean-noncompliant','unexpected proofkind');final.append(c['challenge'])
 if family!='IntegratedPerron':add('Public'+family+version.upper(),R/'Solutions'/(family+'.'+version)/'Solution.lean')
for n in ['BoxMomentNode','BoxMomentEvolution','BoxFullNetwork','ExactBoxFullTypes']:add(n,I/'additive'/(n+'.lean'),True)
need(len(candidates)==32 and len(owned)==19 and len(final)==11 and lit==['IntegratedPerron.v1.formula'],'exact requested new proof universe')
generic={'Mathlib','Lean','Init','Std','Batteries','Aesop','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible'};ordered=[];done=set(basis);active=set()
def visit(mod):
 if mod in done:return
 need(mod in candidates and mod not in active,'missing/cyclic actual module:'+mod);active.add(mod);q=candidates[mod];p=R/q['original_path'];text=p.read_text();need('include_str'not in text and 'include_bin'not in text,'explicit new resource rule required');local=[];gen=[]
 for dep in reader.header_imports(text):
  need('.Challenge'not in dep,'admitted Challenge')
  if dep in basis or dep in candidates:visit(dep);local.append(dep)
  else:need(dep.split('.')[0]in generic,'unmapped application edge:'+mod+' -> '+dep);gen.append(dep)
 q=dict(q,application_imports=local,generic_imports=gen);active.remove(mod);done.add(mod);ordered.append(q)
for mod in candidates:visit(mod)
out=H/'capture';need(not out.exists(),'fresh source capture');src=out/'frozen-source';src.mkdir(parents=True)
for q in ordered:
 p=src/(q['module'].replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes((R/q['original_path']).read_bytes());q['path']=str(p.relative_to(R))
all_final=sorted(read(I/'supplement/audit-corrected-capture/SOURCE_CLOSURE.json')['final_roots']+final);need(len(all_final)==55 and len(set(all_final))==55,'complete55 canonical proof roots')
audit='import Lean\nimport FinalSupplementAudit\n'+''.join('import '+q['module']+'\n'for q in ordered)+'\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let mods := #['+','.join(json.dumps(x)for x in owned)+']\n  let allowed := #[`propext, `Classical.choice, `Quot.sound]\n  let mut count : Nat := 0\n  for (name, idx) in env.const2ModIdx.toList do\n    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous\n    if !mods.contains modName.toString then continue\n    let some (.thmInfo _) := env.find? name | continue\n    let axs ← collectAxioms name\n    unless axs.all allowed.contains do throwError "Nonstandard proof axiom {name}: {axs}"\n    let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),("axioms",toJson (axs.map Name.toString))]\n    logInfo m!"RH_CLOSED_BOX_THEOREM {row.compress}"\n    count := count + 1\n  unless count > 0 do throwError "Empty completed Box audit"\n  logInfo m!"RH_CLOSED_BOX_AUDIT_PASS {count}"\n\nprivate partial def parameterUses : Lean.Expr → List (String × Bool)\n  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body\n  | .mdata _ body => parameterUses body\n  | _ => []\n\nrun_cmd do\n  let env ← getEnv\n  let roots := #['+','.join('`'+x for x in all_final+['RHOcticPush.Network.fully_derived_box_network'])+']\n  let allowed := #[`propext, `Classical.choice, `Quot.sound]\n  for root in roots do\n    let some (.thmInfo info) := env.find? root | throwError "Missing theorem {root}"\n    let axs ← collectAxioms root\n    unless axs.all allowed.contains do throwError "Nonstandard final axiom {root}: {axs}"\n    let ps := (parameterUses info.value).map fun (name,used) => Json.mkObj [("name",toJson name),("used_in_body",toJson used)]\n    let row := Json.mkObj [("theorem",toJson root.toString),("lambda_parameters",toJson ps),("axioms",toJson (axs.map Name.toString))]\n    logInfo m!"RH_CLOSED_BOX_BODY {row.compress}"\n'
p=src/'FinalClosedBoxAudit.lean';p.write_text(audit);ordered.append({'module':'FinalClosedBoxAudit','original_path':None,'path':str(p.relative_to(R)),'sha256':sha(p),'application_imports':['FinalSupplementAudit']+[q['module']for q in ordered],'generic_imports':['Lean']})
manifest={'schema':'RH_CLOSED_BOX33_SOURCE_CLOSURE_V1','foundation_modules':660,'new_modules':33,'owned_modules':owned,'modules':ordered,'roots':[q['module']for q in ordered],'final_roots':all_final,'body_roots':all_final+['RHOcticPush.Network.fully_derived_box_network'],'new_canonical_roots':sorted(final),'literal_sources':lit,'canonical_metadata':metadata,'freezes':[{'path':str(freeze.relative_to(R)),'sha256':sha(freeze)}],'selector_sha256':sha(Path(__file__)),'all_source_count':693,'exact_type_inventory':{'path':str((I/'additive/EXACT_FULL_TYPES.json').relative_to(R)),'sha256':sha(I/'additive/EXACT_FULL_TYPES.json')},'source_claim':'General published Perron remains an explicit B-tier source; both noarg moments and actualzero source adapter supplied. No old Box predicate assumed by final assembledconsumer. No source-firstPV claim.'};(out/'SOURCE_CLOSURE.json').write_text(json.dumps(manifest,indent=2)+'\n');print('captured',len(ordered),'new sources;canonical',len(all_final))
