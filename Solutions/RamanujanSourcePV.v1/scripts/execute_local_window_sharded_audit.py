#!/usr/bin/env python3
"""Complete exact local-proof audit with bounded prime-proof aggregate shards.

Every prescribed prime constant is typechecked and occurs in a checked balanced
conjunction; its aggregate axiom report covers every constituent proof. There is
no heuristic reduction of the requested source/claim universe. Original numerical
algorithms, parameters, proof modules and evidence remain unchanged.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import argparse,hashlib,json,os,re,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
STD3={'propext','Classical.choice','Quot.sound'}
HEADER='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(items):
  out={}
  for k,v in items:need(k not in out,'duplicate JSON key');out[k]=v
  return out
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def publish(p,d):
 t=p.with_name(p.name+'.pending');need(not t.exists(),'fresh atomic stage')
 with t.open('x')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
 t.replace(p)
def reports(text):
 out={}
 pattern=r"'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
 for m in re.finditer(pattern,text,re.S):
  value=set()if m[2]is None else{x.strip()for x in m[2].split(',')if x.strip()}
  need(m[1]not in out or out[m[1]]==value,'consistent named axiom reports');out[m[1]]=value
 return out
def require(table,name,numeric=False):
 need(name in table,'actual compulsory axiom report '+name);need(table[name]<=STD3 and(not numeric or not table[name]),'required proof trust '+name)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--progress',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--width',type=int,required=True);p.add_argument('--jobs',type=int,default=2);p.add_argument('--memory-gib',type=int,default=24);p.add_argument('--cpus',default='16,17');p.add_argument('--shard-size',type=int,default=1024);a=p.parse_args()
 need(1<=a.jobs<=8 and 1<=a.memory_gib<=96 and a.jobs*a.memory_gib<=192,'bounded owner-authorized audit pool');need(1<=a.shard_size<=2048,'bounded exact audit shards')
 available=int(next(l.split()[1]for l in Path('/proc/meminfo').read_text().splitlines()if l.startswith('MemAvailable:')))*1024;need(available>=(512+a.jobs*a.memory_gib)*(1<<30),'preserve512GiB host reserve')
 if a.jobs>4 or a.memory_gib>48:need(available>=1<<40,'large audit pool requires actual available1TiB RAM')
 cpus=[int(x)for x in a.cpus.split(',')];need(len(cpus)==len(set(cpus))and len(cpus)>=a.jobs and set(cpus)<=os.sched_getaffinity(0),'distinct actual worker CPUs')
 mpath=a.manifest.resolve();d=read(mpath);need(d['schema']=='RAMANUJAN_LOCAL_CLASSIFICATION_PROPOSAL_V1'and d['status']=='UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_PROOFS','exact original proposal schema/status');need(56<=a.width<=1000000 and d['bases']==[38358837683,14111427770]and d['unchanged_base_values']==[1644673232,632207037],'locked original base inputs')
 expectedQ=((38358837683+a.width+1)*(1<<60))//3133965575612453533-14111427770;need(d['widths']==[a.width,expectedQ],'exact requested local universe')
 lockpath=S/'evidence/query-locks/CRITICAL_QUERIES.json';lock=read(lockpath);need([(r['N'],r['candidate_value'])for r in lock['required_queries']]==list(zip(d['bases'],d['unchanged_base_values'])),'independent owner query lock')
 ns=d['namespace'];need(re.fullmatch(r'RamanujanPV\.[A-Za-z][A-Za-z0-9_]*',ns)is not None,'exact namespace');root=Path(d['source_root']).resolve();mods={m['module']:m for m in d['modules']};need(len(mods)==len(d['modules']),'unique compiler identities');sources=[Path(m['source']).resolve()for m in d['modules']];need(len(sources)==len(set(sources))and set(sources)==set(root.rglob('*.lean')),'complete exact original source population')
 for m in mods.values():need(sha(m['source'])==m['sha256'],'every unchanged original source')
 progress=read(a.progress);need(progress['status']in ['PARTIAL_NOT_ACCEPTANCE','COMPLETED_HOST_LOCAL_KERNEL_INCREMENT_PROOFS_BASE_PAIR_PENDING_NOT_SOURCE_PV_ALONE'],'partial ledger never acceptance');original={r['module']:r for r in progress['records']};need(len(original)==len(progress['records'])and set(original)==set(mods),'ALL original compiled modules required')
 context=read(S/'BUILD_CONTEXT.json');objects=Path(context['new_application_object_root']);scratch=objects.resolve().parent;compiler_hash=sha(context['compiler']);context_hash=sha(S/'BUILD_CONTEXT.json');scientific={str(S/'RamanujanPV'/n):sha(S/'RamanujanPV'/n)for n in ['PrimeWindow.lean','LocalWindowCode.lean','LocalLucas.lean','LocalPrimeTree.lean']};records=[]
 for name,m in mods.items():
  old=original[name];need(old['source_sha256']==m['sha256']and sha(old['receipt'])==old['receipt_sha256'],'exact original source/receipt '+name);q=Path(old['receipt']);r=read(q);folder=q.parent
  need(r['status']=='COMPILED'and r['returncode']==0 and r['module']==name and r['source_sha256']==m['sha256']and r['source_unchanged_during_compile']is True and r['compiler_sha256']==compiler_hash and r['generic_dependency_context_sha256']==context_hash,'actual current compiled source/compiler '+name)
  need(sha(folder/'source.lean')==m['sha256']and sha(objects/Path(*name.split('.')).with_suffix('.olean'))==r['object_sha256']==old['object_sha256'],'actual source snapshot/object '+name)
  for f,k in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(folder/f)==r[k],'exact original compiler log')
  text=(folder/'stdout').read_text();errors=(folder/'stderr').read_text();need(not any(x in text+errors for x in ['sorryAx','Lean.ofReduceBool','declaration uses `sorry`']),'forbidden original proof leaf');table=reports(text)
  for short in m['mandatory_axioms']:require(table,ns+'.'+short,m['kind']=='check')
  records.append(old)
 primes=[c['p']for c in d['certificate_parameters']];need(primes and len(primes)==len(set(primes))and all(type(n)is int and n>=2 for n in primes),'complete unique prescribed prime identities')
 out=a.out.resolve();need(out.is_relative_to(scratch)and not out.exists(),'fresh experiment-owned supplemental audit');out.mkdir(parents=True);croot=out/'controller-source';croot.mkdir();started=time.monotonic();prefix='RamanujanPV.LocalWindowSharded_'+sha(mpath)[:16];tasks=[];coverage=[]
 def tree(values,lo,hi):
  if hi-lo==1:return '(.leaf '+str(values[lo])+')'
  mid=(lo+hi)//2;return '(.branch '+str(mid)+' '+tree(values,lo,mid)+' '+tree(values,mid,hi)+')'
 def proof(values,lo,hi):
  if hi-lo==1:return ns+'.prime_'+str(values[lo])
  mid=(lo+hi)//2;return '⟨'+proof(values,lo,mid)+','+proof(values,mid,hi)+'⟩'
 for part,lo in enumerate(range(0,len(primes),a.shard_size)):
  values=primes[lo:lo+a.shard_size];module=prefix+'.Prime'+str(part).zfill(4);path=croot/Path(*module.split('.')).with_suffix('.lean');path.parent.mkdir(parents=True,exist_ok=True);symbol=module+'.all_required_primes'
  lines=[HEADER+'import '+d['final_module'],'import RamanujanPV.LocalPrimeTree','namespace '+module,'set_option maxHeartbeats 0','set_option maxRecDepth 100000','set_option Elab.async false']
  for n in values:lines.append('example : Nat.Prime '+str(n)+' := '+ns+'.prime_'+str(n))
  lines+=['def required_tree : Lean.RArray Nat := '+tree(values,0,len(values)),'theorem all_required_primes : RamanujanPV.LocalPrimeTree.PrimeTreeGood required_tree := '+proof(values,0,len(values)),'#print axioms '+symbol,'end '+module];path.write_text('\n'.join(lines)+'\n');tasks.append(dict(module=module,source=str(path),source_sha256=sha(path),symbols=[(symbol,False)],prime_range=[lo,lo+len(values)]));coverage+=list(range(lo,lo+len(values)))
 need(coverage==list(range(len(primes))),'disjoint exhaustive ordered prime audit coverage')
 module=prefix+'.Consumers';path=croot/Path(*module.split('.')).with_suffix('.lean');lines=[HEADER+'import '+d['final_module'],'open RamanujanPV','open QuotientDemandCheck','namespace '+module,'set_option maxHeartbeats 0','set_option maxRecDepth 100000','set_option Elab.async false'];symbols=[]
 lines+=['example : LocalPrimeTree.PrimeTreeGood '+ns+'.primes := '+ns+'.primes_good','#print axioms '+ns+'.primes_good'];symbols.append((ns+'.primes_good',False))
 for side,base,width in zip(['p','q'],d['bases'],d['widths']):
  for part,lo in enumerate(range(0,width,d['check_chunk'])):
   size=min(d['check_chunk'],width-lo);name=ns+'.part_'+side+'_'+str(part).zfill(4);lines+=['example : allFrom (PrimeWindow.checkEntry '+str(base)+' '+ns+'.primes '+ns+'.primeCount '+ns+'.'+side+'Entries) '+str(lo)+' '+str(size)+' = true := '+name,'#print axioms '+name];symbols.append((name,True))
  name=ns+'.'+side+'_increment';lines+=['example (i : Nat) (hi : i < '+str(width)+') : Nat.primeCounting ('+str(base)+'+i+1) = Nat.primeCounting '+str(base)+' + ('+ns+'.'+side+'Entries.get i).cumulative := '+name+' i hi','#print axioms '+name];symbols.append((name,False))
 for side,base,width,delta in zip(['p','q'],d['bases'],d['widths'],d['endpoint_deltas']):
  value=module+'.'+side+'_last_value';endpoint=module+'.'+side+'_endpoint';lines+=['theorem '+side+'_last_value : ('+ns+'.'+side+'Entries.get '+str(width-1)+').cumulative = '+str(delta)+' := by decide +kernel','#print axioms '+value,'theorem '+side+'_endpoint : Nat.primeCounting '+str(base+width)+' = Nat.primeCounting '+str(base)+' + '+str(delta)+' := by','  have h := '+ns+'.'+side+'_increment '+str(width-1)+' (by decide)','  simpa only ['+side+'_last_value] using h','#print axioms '+endpoint];symbols.extend([(value,True),(endpoint,False)])
 lines+=['end '+module];path.write_text('\n'.join(lines)+'\n');tasks.append(dict(module=module,source=str(path),source_sha256=sha(path),symbols=symbols,prime_range=None));publish(out/'AUDIT_PLAN.json',dict(manifest_sha256=sha(mpath),prescribed_prime_count=len(primes),ordered_prime_symbols=[ns+'.prime_'+str(n)for n in primes],prime_coverage=coverage,tasks=tasks))
 def compile_one(task,cpu):
  command=[sys.executable,str(S/'scripts/compile_lean.py'),task['module'],'--source-root',str(croot),'--audit-root',str(out/'audit'),'--memory-gib',str(a.memory_gib),'--cpus',str(cpu)];r=subprocess.run(command,capture_output=True,text=True);log=out/(task['module']+'.stdout');log.write_text(r.stdout);(out/(task['module']+'.stderr')).write_text(r.stderr);need(r.returncode==0,'actual audit shard compilation '+task['module']);folder=Path(json.loads(r.stdout.strip().splitlines()[-1])['audit']);receipt=read(folder/'RUN.json');need(receipt['status']=='COMPILED'and receipt['source_sha256']==task['source_sha256']and receipt['source_unchanged_during_compile']is True and receipt['compiler_sha256']==compiler_hash,'actual shard source/compiler')
  need(sha(folder/'source.lean')==task['source_sha256']and sha(objects/Path(*task['module'].split('.')).with_suffix('.olean'))==receipt['object_sha256'],'actual audited shard object/snapshot');text=(folder/'stdout').read_text();table=reports(text)
  for name,numeric in task['symbols']:require(table,name,numeric)
  need(all(sha(p)==h for p,h in scientific.items()),'unchanged scientific definitions');return dict(module=task['module'],source=task['source'],source_sha256=task['source_sha256'],receipt=str(folder/'RUN.json'),receipt_sha256=sha(folder/'RUN.json'),prime_range=task['prime_range'],seconds=receipt['elapsed_seconds'])
 # The first real shard profiles the complete imported original proof closure.
 audited=[compile_one(tasks[0],cpus[0])];pending=iter(tasks[1:]);active={};idle=cpus[:a.jobs]
 with ThreadPoolExecutor(max_workers=a.jobs)as pool:
  while True:
   while idle:
    task=next(pending,None)
    if task is None:break
    cpu=idle.pop(0);active[pool.submit(compile_one,task,cpu)]=cpu
   if not active:break
   done,_=wait(active,return_when=FIRST_COMPLETED)
   for future in done:idle.append(active.pop(future));audited.append(future.result());publish(out/'PROGRESS.json',dict(status='PARTIAL_SHARDED_AUDIT_NOT_ACCEPTANCE',completed=len(audited),total=len(tasks),records=audited))
 need(len(audited)==len(tasks),'all exact audit shards and final consumers completed');need(sorted(r['prime_range']for r in audited if r['prime_range']is not None)==[t['prime_range']for t in tasks if t['prime_range']is not None],'every disjoint prime shard accepted')
 prime_tasks=[t for t in tasks if t['prime_range']is not None]
 def collective_type(lo,hi):
  if hi-lo==1:return 'RamanujanPV.LocalPrimeTree.PrimeTreeGood '+prime_tasks[lo]['module']+'.required_tree'
  mid=(lo+hi)//2;return '('+collective_type(lo,mid)+' ∧ '+collective_type(mid,hi)+')'
 def collective_proof(lo,hi):
  if hi-lo==1:return prime_tasks[lo]['module']+'.all_required_primes'
  mid=(lo+hi)//2;return '⟨'+collective_proof(lo,mid)+','+collective_proof(mid,hi)+'⟩'
 collective=prefix+'.Collective';cp=croot/Path(*collective.split('.')).with_suffix('.lean');consumer=prefix+'.Consumers'
 clines=[HEADER]+['import '+t['module']for t in tasks]+['namespace '+collective,'set_option maxHeartbeats 0','set_option maxRecDepth 100000','set_option Elab.async false','theorem all_prescribed_prime_proofs : '+collective_type(0,len(prime_tasks))+' := '+collective_proof(0,len(prime_tasks)),'#print axioms '+collective+'.all_prescribed_prime_proofs'];csymbols=[(collective+'.all_prescribed_prime_proofs',False)]
 for side,base,width,delta in zip(['p','q'],d['bases'],d['widths'],d['endpoint_deltas']):
  name=collective+'.'+side+'_endpoint';clines+=['theorem '+side+'_endpoint : Nat.primeCounting '+str(base+width)+' = Nat.primeCounting '+str(base)+' + '+str(delta)+' := '+consumer+'.'+side+'_endpoint','#print axioms '+name];csymbols.append((name,False))
 clines+=['end '+collective];cp.write_text('\n'.join(clines)+'\n');ctask=dict(module=collective,source=str(cp),source_sha256=sha(cp),symbols=csymbols,prime_range=None);publish(out/'COLLECTIVE_PLAN.json',dict(source_sha256=ctask['source_sha256'],dependencies=[r['module']for r in audited],exact_prime_count=len(primes)));collective_record=compile_one(ctask,cpus[0])
 result=dict(status='COMPLETED_HOST_LOCAL_KERNEL_INCREMENT_PROOFS_BASE_PAIR_PENDING_NOT_SOURCE_PV_ALONE',manifest=str(mpath),manifest_sha256=sha(mpath),widths=d['widths'],bases=d['bases'],endpoint_deltas=d['endpoint_deltas'],actual_local_primes=d['actual_local_primes'],all_certificate_primes=d['all_certificate_primes'],scientific_sources=scientific,seconds=time.monotonic()-started,records=records,sharded_exact_type_and_aggregate_axiom_audit=True,prescribed_prime_count=len(primes),exact_prime_types_checked=len(primes),aggregate_shard_size=a.shard_size,audit_plan_sha256=sha(out/'AUDIT_PLAN.json'),audit_shards=audited,sharded_audit=dict(exact_coverage=True,source_plan=str(out/'AUDIT_PLAN.json'),source_plan_sha256=sha(out/'AUDIT_PLAN.json'),collective_plan_sha256=sha(out/'COLLECTIVE_PLAN.json'),shards=audited,collective=collective_record),controller_source=str(cp),controller_source_sha256=sha(cp),controller_receipt=collective_record['receipt'],controller_receipt_sha256=collective_record['receipt_sha256'],base_pair_closed_here=False,full_finite_Ramanujan_claimed=False,controller_sha256=sha(__file__),posthoc_audit_only=True,no_original_proofs_or_results_changed=True,owner_query_lock_sha256=sha(lockpath));publish(out/'RESULT.json',result);print(json.dumps({k:result[k]for k in ['status','widths','exact_prime_types_checked','seconds']},sort_keys=True))
if __name__=='__main__':main()
