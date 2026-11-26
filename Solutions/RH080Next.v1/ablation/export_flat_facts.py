#!/usr/bin/env python3
"""Export all compiler-identified statement types/ordinary definition values.
The mathematical statement corpus is common to every experimental arm. Theorem
proof bodies and authored source graphs are the assigned treatment, not facts.
"""
from pathlib import Path
import argparse,json,hashlib,subprocess,os,re,time,sys
sys.setrecursionlimit(200000)

def need(ok,message):
 if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def unique(items):
 d={}
 for k,v in items:
  need(k not in d,'Duplicate JSON key');d[k]=v
 return d
def load(p):return json.loads(p.read_bytes(),object_pairs_hook=unique,parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--support',type=Path,required=True);p.add_argument('--context',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'Fresh export required');a.out.mkdir();c=load(a.context);need(sha(Path(c['compiler']))==c['compiler_sha256'],'Compiler differs');modules=load(a.support/'EXPOSURE.json')['application_modules']+['RH080EstimatePack'];need(len(modules)==len(set(modules))and all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*',m)for m in modules),'Exact module identity required')
code='''import RH080EstimatePack
import PopulationActualConsumers
import Lean
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option pp.maxSteps 100000000
set_option pp.all false
set_option pp.proofs false
set_option pp.fullNames true
set_option pp.deepTerms false
open Lean Elab Command Meta

structure TermStore where
  cache : Std.HashMap Expr Nat := {}
  nodes : Array Json := #[]

partial def termId (e : Expr) : StateM TermStore Nat := do
  if let some i := (←get).cache[e]? then return i
  let row ← match e with
    | .bvar n => pure (toJson ([toJson "bvar",toJson n] : List Json))
    | .sort u => pure (toJson ([toJson "sort",toJson (toString u)] : List Json))
    | .const n us => pure (toJson ([toJson "const",toJson n.toString,toJson (us.map toString)] : List Json))
    | .app f x => do let f ← termId f; let x ← termId x; pure (toJson ([toJson "app",toJson f,toJson x] : List Json))
    | .lam n t b bi => do let t ← termId t; let b ← termId b; pure (toJson ([toJson "lambda",toJson n.toString,toJson (reprStr bi),toJson t,toJson b] : List Json))
    | .forallE n t b bi => do let t ← termId t; let b ← termId b; pure (toJson ([toJson "forall",toJson n.toString,toJson (reprStr bi),toJson t,toJson b] : List Json))
    | .letE n t v b nd => do let t ← termId t; let v ← termId v; let b ← termId b; pure (toJson ([toJson "let",toJson n.toString,toJson t,toJson v,toJson b,toJson nd] : List Json))
    | .lit (.natVal n) => pure (toJson ([toJson "nat",toJson (toString n)] : List Json))
    | .lit (.strVal s) => pure (toJson ([toJson "string",toJson s] : List Json))
    | .mdata _ e => do let i ← termId e; pure (toJson ([toJson "metadata-erased",toJson i] : List Json))
    | .proj n i e => do let e ← termId e; pure (toJson ([toJson "projection",toJson n.toString,toJson i,toJson e] : List Json))
    | .fvar n => pure (toJson ([toJson "unexpected-free-variable",toJson n.name.toString] : List Json))
    | .mvar n => pure (toJson ([toJson "unexpected-metavariable",toJson n.name.toString] : List Json))
  let s ← get
  let i := s.nodes.size
  set ({cache:=s.cache.insert e i,nodes:=s.nodes.push row} : TermStore)
  return i

def exposed : List Name := MODULES

run_cmd do
  let env ← getEnv
  for n in exposed do
    unless env.header.moduleNames.contains n do throwError "Missing exposed module {n}"
  let mut rows : Array Json := #[]
  let mut terms : TermStore := {}
  let mut text := "# Complete shared compiled mathematical statements\\n\\nTheorem/proof bodies are omitted; ordinary non-proof definitions are included.\\nThe exact selection is every imported compiler declaration belonging to the169 selected application modules.\\n\\n"
  let moduleMask := env.header.moduleNames.map (fun n => exposed.contains n)
  let selected := env.constants.toList.filter (fun pair =>
    match env.getModuleIdxFor? pair.1 with
    | some i => moduleMask[i]!
    | none => false)
  let constants := selected.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  for (name,info) in constants do
    if let some i := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[i]!
      if exposed.contains moduleName then
        let proof ← liftTermElabM <| Meta.isProp info.type
        let renderedType ← liftTermElabM <| Meta.ppExpr info.type
        let (typeId,nextTerms) := (termId info.type).run terms
        terms := nextTerms
        let mut row := [("module",toJson moduleName.toString),("declaration",toJson name.toString),("is_proof",toJson proof),("type",toJson typeId),("readable_type",toJson renderedType.pretty)]
        text := text++"Declaration: "++name.toString++"\\nType: "++renderedType.pretty++"\\n"
        if !proof then
          if let some value := info.value? then
            let renderedValue ← liftTermElabM <| Meta.ppExpr value
            let (valueId,nextTerms) := (termId value).run terms
            terms := nextTerms
            row := row++[("definition",toJson valueId),("readable_definition",toJson renderedValue.pretty)]
            text := text++"Definition: "++renderedValue.pretty++"\\n"
        text := text++"\\n"
        rows := rows.push (Json.mkObj row)
  liftIO <| IO.FS.writeFile "NODES_PATH" (Json.compress (toJson terms.nodes))
  liftIO <| IO.FS.writeFile "JSON_PATH" (Json.compress (toJson rows))
  liftIO <| IO.FS.writeFile "TEXT_PATH" text
  logInfo m!"COMPLETE_EXPOSURE_FACTS modules={exposed.length} declarations={rows.size}"
'''
code=code.replace('MODULES','['+','.join('`'+m for m in modules)+']').replace('JSON_PATH',str(a.out/'FLAT_FACTS.json')).replace('TEXT_PATH',str(a.out/'FLAT_FACTS.txt')).replace('NODES_PATH',str(a.out/'TERM_NODES.json'));source=a.out/'ExportFacts.lean';source.write_text(code);env=dict(os.environ,LEAN_PATH=str(a.support/'objects')+':'+c['generic_lean_path']);start=time.monotonic();command=[c['compiler'],'-j1','--root='+str(a.out),str(source)]
with(a.out/'stdout').open('x')as out,(a.out/'stderr').open('x')as err:r=subprocess.run(command,env=env,stdout=out,stderr=err)
need(r.returncode==0,'Compiler fact exporter failed; exact logs preserved');diagnostic=(a.out/'stdout').read_text()+'\n'+(a.out/'stderr').read_text();need(re.search(r'PANIC|error:',diagnostic,re.I)is None,'Exporter diagnostics');rows=load(a.out/'FLAT_FACTS.json');keys=[(x['module'],x['declaration'])for x in rows];need(len(keys)==len(set(keys)),'Collapsed compiler declaration identity');need(all(x['module']in modules for x in rows),'Unassigned module exported');raw=(a.out/'TERM_NODES.json').read_text();need('unexpected-free-variable'not in raw and'unexpected-metavariable'not in raw,'Unclosed declaration in fact corpus');result={'status':'PASS_COMPLETE_SELECTED_COMPILER_STATEMENT_CORPUS_NOT_A_SOURCE_CLAIM_AUDIT','modules':modules,'declarations':len(rows),'theorem_or_proof_statements':sum(x['is_proof']for x in rows),'ordinary_definitions':sum('definition'in x for x in rows),'scope':'All compiler declaration types from selected application modules; all ordinary non-proof definition values; theorem/proof bodies omitted. No claim of auditing every IEANTN source attribution.','selection_creator':'coordinator /root; exact compiled proof closure for3 existing curves and actual source-first alternatives','statement_json_sha256':sha(a.out/'FLAT_FACTS.json'),'statement_text_sha256':sha(a.out/'FLAT_FACTS.txt'),'exact_term_nodes_sha256':sha(a.out/'TERM_NODES.json'),'readable_display_may_abbreviate':True,'exact_term_graph_is_authoritative':True,'export_source_sha256':sha(source),'export_driver_sha256':sha(Path(__file__)),'compiler_sha256':c['compiler_sha256'],'command':command,'seconds':time.monotonic()-start,'model_calls':0};(a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS_COMMON_FACTS',len(modules),len(rows))
