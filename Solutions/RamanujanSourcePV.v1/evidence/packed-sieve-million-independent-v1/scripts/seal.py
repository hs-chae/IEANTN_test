#!/usr/bin/env python3
"""Read exact compiled audit, whole actual application source/object universe, and receipts.
No scientific source is edited, and no new mathematical execution is inferred from native data.
"""
from pathlib import Path
import argparse,collections,hashlib,json,math,re,sys,time
S=Path(__file__).resolve().parents[0] # overwritten by explicit pinned location below
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1')
D=Path('/data/ivy-ramanujan-source-pv-20261119')
def need(x,m):
 if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pairs(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
 return d
def reject(x):raise ValueError('nonfinite JSON')
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=reject)
def dump(p,d):Path(p).write_text(json.dumps(d,indent=2,sort_keys=True)+'\n')
def audited(p,source=None,obj=None):
 p=Path(p);r=read(p);need(r['status']=='COMPILED'and r['returncode']==0,'actual successful compiler receipt')
 need(r['compiler_sha256']==context['compiler_sha256']==sha(context['compiler']),'actual compiler identity')
 need(r['generic_dependency_context_sha256']==sha(S/'BUILD_CONTEXT.json'),'exact generic context')
 source=Path(source or r['source']);need(sha(source)==r['source_sha256'],'current exact source')
 cmd=r['command'];obj=Path(obj or cmd[len(cmd)-1-cmd[::-1].index('-o')+1]);need(obj.is_file()and sha(obj)==r['object_sha256'],'current exact object')
 original=Path(r['source']);need(original.is_file()and sha(original)==r['source_sha256'],'original source receipt path')
 for name,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(p.parent/name)==r[key],name+' exact identity')
 snapshot=p.parent/'source.lean'
 if snapshot.exists():need(sha(snapshot)==r['source_sha256'],'frozen compiler source snapshot')
 return {'module':r['module'],'source':str(source),'source_sha256':sha(source),'compiler_source':str(original),'object':str(obj),'object_sha256':sha(obj),'receipt':str(p),'receipt_sha256':sha(p),'compiler_snapshot_present':snapshot.exists(),'seconds':r['elapsed_seconds'],'stdout_sha256':r['stdout_sha256'],'stderr_sha256':r['stderr_sha256'],'rusage_sha256':r['rusage_sha256']}
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--audit-dir',type=Path,default=S/'audit/RamanujanPV.PackedSieveMillionIndependentAudit/2');a=p.parse_args();started=time.monotonic();context=read(S/'BUILD_CONTEXT.json')
audit=audited(a.audit_dir/'RUN.json');need(audit['source_sha256']=='01413622f373a3b3adf0ff51cbb0ca1a235d391aa8d838b2fb0ff7184f1b65c5','independently fixed audit bytes')
t=(a.audit_dir/'stdout').read_text();mods=re.findall(r'^PACKED_ACTUAL_IMPORTED_MODULE (.+)$',t,re.M);need(len(mods)==len(set(mods))==11248,'complete actual compiler import universe')
rootnames=['RamanujanPV.PackedSieveMillion.complete_certificate','RamanujanPV.PackedSieveMillion.first_1000001_real_interval','RamanujanPV.PackedSieveMillion.uniform_gap']
counts=[59227,59259,59266];rootFacts=[]
for name,count,binders in zip(rootnames,counts,[0,3,3]):
 need(t.count('PACKED_MILLION_COMPLETE_CONSTANT_CLOSURE '+name+' '+str(count)+'\n')==1,'complete separate root closure')
 need(t.count('PACKED_MILLION_BINDER_COUNT '+name+' '+str(binders)+'\n')==1,'no additional source/count assumptions')
 m=re.search(r'^PACKED_MILLION_COMPLETE_AXIOM_UNIVERSE '+re.escape(name)+r' \[([^]]+)\]',t,re.M);need(m is not None,'mandatory separate root axiom report');axes=[x.strip()for x in m.group(1).split(',')];need(set(axes)=={'propext','Classical.choice','Quot.sound'},'complete standard-only axioms')
 paths=re.findall(r'^PACKED_MILLION_CHECKED_PATH '+re.escape(name)+r': (.+)$',t,re.M);need(len(paths)==47+([0,3,5][rootnames.index(name)]),'every required path checked')
 rootFacts.append(dict(root=name,complete_type_and_proof_constants=count,binders=binders,axioms=axes,required_paths=paths))
app=[n for n in mods if(D/'lean'/Path(*n.split('.')).with_suffix('.olean')).is_file()];need(len(app)==548,'exact current application import universe')
roots=[S,S.parents[1]]+[D/n/'source'for n in ['demand-critical-pair-v3','finite-cell-domains-million-v1','finite-cell-million-v1','finite-scalar-million-v1','local-cells-million-v1','local-window-million-v1','packed-sieve-mask-profile-v1','packed-sieve-primitive-v1']]
recordCandidates={}
for q in [D/'demand-critical-pair-v3/final-run-v1/RESULT.json',D/'local-window-million-v1/sharded-final-v1/RESULT.json',D/'local-cells-million-v1/run-v1/RESULT.json']:
 if q.is_file():
  for row in read(q).get('records',[]):
   receipt=row.get('compiler_receipt',row.get('receipt'))
   if receipt:recordCandidates.setdefault(row['module'],[]).append(Path(receipt))
extraAudits=[D/n/rel for n,rel in [('finite-cell-domains-million-v1','source/audit'),('finite-cell-million-v1','source/audit'),('finite-scalar-million-v1','source/audit'),('packed-sieve-mask-profile-v1','audit'),('packed-sieve-primitive-v1','audit')]]
associations=[];sourceMap={}
for name in app:
 relative=Path(*name.split('.')).with_suffix('.lean');candidates=[r/relative for r in roots if(r/relative).is_file()];need(candidates,'source exists for '+name);source=candidates[0];sourceMap[name]=source
 objectFile=D/'lean'/relative.with_suffix('.olean');h=sha(source);oh=sha(objectFile)
 receipts=list((S/'audit'/name).glob('*/RUN.json'))+recordCandidates.get(name,[])
 for ar in extraAudits:receipts.extend((ar/name).glob('*/RUN.json'))
 accepted=[]
 for q in receipts:
  d=read(q)
  if d.get('status')=='COMPILED'and d.get('source_sha256')==h and d.get('object_sha256')==oh:accepted.append(q)
 need(accepted,'matching receipt for '+name);associations.append(audited(accepted[0],source,objectFile))
seen=set();todo=['RamanujanPV.PackedSieveMillion'];appset=set(app)
while todo:
 name=todo.pop()
 if name in seen:continue
 seen.add(name)
 for line in sourceMap[name].read_text().splitlines():
  if line.startswith('import '):
   for dep in line.split()[1:]:
    if dep in appset:todo.append(dep)
need(seen==appset,'actual whole application source-import reachability, no added audit appmodules')
oldRaw=[n for n in app if n.startswith('RamanujanPV.LocalWindowMillion.')]
expectedOldRaw=['RamanujanPV.LocalWindowMillion.PrimeValues','RamanujanPV.LocalWindowMillion.Data']+['RamanujanPV.LocalWindowMillion.EntriesP'+str(i).zfill(4)for i in range(31)]+['RamanujanPV.LocalWindowMillion.EntriesQ'+str(i).zfill(4)for i in range(12)]
need(set(oldRaw)==set(expectedOldRaw),'precise unchanged incidental raw-data modules')
for name in oldRaw:
 text=sourceMap[name].read_text();need(not re.search(r'(?m)^\s*(theorem|lemma|axiom)\s',text),'incidental old module is raw definitions only')
for name in app:
 need(not any(name.startswith(pre)for pre in ['RamanujanPV.LocalLucas','RamanujanPV.LocalPrimeTree','RamanujanPV.LocalCells1000','RamanujanPV.LocalWindowMillion.Primes','RamanujanPV.LocalWindowMillion.PrimeProof','RamanujanPV.LocalWindowMillion.Check','RamanujanPV.LocalWindowMillion.Final','RamanujanPV.CriticalSourceClosed','RamanujanPV.SegmentSourceMargins','RamanujanPV.FiniteGuardedMillion','RamanujanPV.FiniteProgramMillion']),'forbidden old proof module '+name)
extraCount=audited(S/'audit/RamanujanPV.PackedSieveCounts/1/RUN.json');optionalText=(S/'audit/RamanujanPV.PackedSieveCounts/1/stdout').read_text()
for name in ['p_population','p_source','p_primeCounting']:
 match=re.search("'RamanujanPV.PackedSieveCounts."+name+r"' depends on axioms: \[([^]]+)\]",optionalText);need(match is not None and set(x.strip()for x in match.group(1).split(','))=={'propext','Classical.choice','Quot.sound'},'optional exact population/source count axioms')
usage=(a.audit_dir/'rusage.txt').read_text();rss=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',usage).group(1))*1024
result=dict(status='PASS_INDEPENDENT_PACKED_MILLION_COMPLETE_CLOSURES_AND_CURRENT_IMPORTS',scope='Three frozen current mathematical roots, actual proof/type and source import universes; optional whole-P population readback separately',audit=audit,root_closures=rootFacts,actual_imported_modules_count=len(mods),current_application_module_count=len(app),application_definition='Every actual environment imported module with its selected object in the pinned fresh application object root; all548 individually source/object/compiler/log associated and source-reachable from PackedSieveMillion',generic_imported_modules_count=len(mods)-len(app),all_actual_imports=mods,application_modules=associations,incidental_legacy_raw_data_count=len(oldRaw),incidental_legacy_raw_data_modules=oldRaw,legacy_raw_data_explanation='Locked LocalCellsMillion.Data retains its original import and unused rowCheck. These45 imports define only raw arrays/counts; every LocalWindowMillion constant is absent from all three final proof/type closures. No old Lucas/primality/classifier/final provider modules are imported.',forbidden_exact_constants=re.findall(r'^PACKED_FORBIDDEN_EXACT (.+)$',t,re.M),forbidden_constant_prefixes=re.findall(r'^PACKED_FORBIDDEN_PREFIX (.+)$',t,re.M),optional_whole_P_count=dict(receipt=extraCount,population=40916,hi=38359837683,primeCounting=1644714148,not_new_main_audit_root=True,proof='Original final prefix via proved slices and byte-width theorem; no repeated whole-mask popcount evaluation'),resources=dict(audit_elapsed_seconds=read(a.audit_dir/'RUN.json')['elapsed_seconds'],peak_RSS_bytes=rss,address_space_limit_bytes=48*1024**3,OOM_events=0),trust_boundaries=['Actual unchanged C function contracts and exact source-byte/AST binding are on the proof path. Existing quotient and segmented C models close count correctness; source scalar helper/guard executions close numerical predicates.','Mathematical canonical inputHeap construction derives allocated ownership and all claims. A physical C loader/caller populating these claims from zeroed arrays and the native packed producer are not verified by this result.','Pinned generic compiler/core runtime, precise arithmetic/ABI assumptions, OS and hardware remain documented external trust boundaries; ordinary native observations are supplemental.','Non-strict original285-row Domain facts are kernel checked and legitimately consumed; strict positivity is derived from actual source cell return1, not old row strict facts.'],source_claim_scope='Project-internal packed representation/checker derivations and unchanged C source contracts only. No new external theorem claim or official Blueprint node is asserted; actual mathematical consumer uses IEANTN primeCounting. Not an exhaustive literature/source census.',readback_seconds=time.monotonic()-started,python_optimization=sys.flags.optimize)
a.out.parent.mkdir(parents=True,exist_ok=True);need(not a.out.exists(),'fresh atomic readback output');temp=a.out.with_suffix(a.out.suffix+'.tmp');dump(temp,result);temp.replace(a.out);print(json.dumps({k:result[k]for k in ['status','current_application_module_count','incidental_legacy_raw_data_count','readback_seconds','python_optimization']}))
