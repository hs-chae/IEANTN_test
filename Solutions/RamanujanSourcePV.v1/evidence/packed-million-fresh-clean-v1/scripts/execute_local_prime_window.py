#!/usr/bin/env python3
"""Bounded actual Lean local-increment certificate execution; not PV by itself."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor,wait,FIRST_COMPLETED
import argparse,hashlib,json,os,re,subprocess,sys,time
S=Path(__file__).resolve().parents[1]
STD3={'propext','Classical.choice','Quot.sound'}
def need(value,message):
 if not value:raise ValueError(message)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs)
def publish(p,d):
 t=p.with_suffix('.pending');need(not t.exists(),'fresh atomic stage')
 with t.open('x')as f:json.dump(d,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
 t.replace(p)
def axioms(text,name,numerical=False):
 no=re.search("'"+re.escape(name)+"' does not depend on any axioms",text)
 yes=re.search("'"+re.escape(name)+r"' depends on axioms:\s*\[([^\]]*)\]",text,re.S)
 need(no is not None or yes is not None,'actual named axiom report '+name)
 found=set()if no else{x.strip()for x in yes[1].split(',')if x.strip()}
 need(found<=STD3 and(not numerical or not found),'actual theorem trust '+name)
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--width',type=int,required=True);p.add_argument('--jobs',type=int,default=2);p.add_argument('--cpus',default='4,5');p.add_argument('--memory-gib',type=int,default=24);a=p.parse_args()
 need(1<=a.jobs<=8 and 1<=a.memory_gib<=96 and a.jobs*a.memory_gib<=192,'bounded owner authorized pool')
 available=int(next(line.split()[1]for line in Path('/proc/meminfo').read_text().splitlines()if line.startswith('MemAvailable:')))*1024
 need(available>=(512+a.jobs*a.memory_gib)*(1<<30),'preserve512GiB host reserve')
 if a.jobs>4 or a.memory_gib>48:need(available>=1<<40,'large proof pool requires actual available1TiB RAM')
 cpus=[int(x)for x in a.cpus.split(',')];need(len(cpus)>=a.jobs and len(cpus)==len(set(cpus))and set(cpus)<=os.sched_getaffinity(0),'actual distinct worker CPUs')
 mpath=a.manifest.resolve();d=read(mpath);need(d['schema']=='RAMANUJAN_LOCAL_CLASSIFICATION_PROPOSAL_V1'and d['status']=='UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_PROOFS','exact proposal schema/status')
 need(56<=a.width<=1000000 and d['bases']==[38358837683,14111427770]and d['unchanged_base_values']==[1644673232,632207037],'locked actual base inputs')
 expectedQ=((38358837683+a.width+1)*(1<<60))//3133965575612453533-14111427770;need(d['widths']==[a.width,expectedQ],'exact requested local query universe')
 need(re.fullmatch(r'RamanujanPV\.[A-Za-z][A-Za-z0-9_]*',d['namespace'])is not None,'exact namespace');ns=d['namespace'];root=Path(d['source_root']).resolve();mods={x['module']:x for x in d['modules']};need(len(mods)==len(d['modules']),'unique module identities')
 sources=[Path(x['source']).resolve()for x in d['modules']];need(len(sources)==len(set(sources))and set(sources)==set(root.rglob('*.lean')),'complete exact source population')
 for m in mods.values():need(sha(m['source'])==m['sha256'],'exact source '+m['module'])
 out=a.out.resolve();need(not out.exists(),'fresh supplemental execution');out.mkdir(parents=True);start=time.monotonic();context=read(S/'BUILD_CONTEXT.json');objects=Path(context['new_application_object_root']);records={};pending=set(mods);active={};idle=cpus[:a.jobs]
 scientific={str(S/'RamanujanPV'/n):sha(S/'RamanujanPV'/n)for n in ['PrimeWindow.lean','LocalWindowCode.lean','LocalLucas.lean','LocalPrimeTree.lean']}
 def compile_one(name,cpu):
  m=mods[name];command=[sys.executable,str(S/'scripts/compile_lean.py'),name,'--source-root',str(root),'--audit-root',str(out/'audit'),'--memory-gib',str(a.memory_gib),'--cpus',str(cpu)]
  result=subprocess.run(command,capture_output=True,text=True);(out/(name+'.stdout')).write_text(result.stdout);(out/(name+'.stderr')).write_text(result.stderr);need(result.returncode==0,'actual compile '+name)
  folder=Path(json.loads(result.stdout.strip().splitlines()[-1])['audit']);r=read(folder/'RUN.json');need(r['status']=='COMPILED'and r['source_sha256']==m['sha256']and r['source_unchanged_during_compile']is True,'actual compiled source '+name)
  need(sha(folder/'source.lean')==m['sha256']and sha(objects/Path(*name.split('.')).with_suffix('.olean'))==r['object_sha256'],'actual object/snapshot '+name)
  text=(folder/'stdout').read_text();need(not any(s in text for s in ['sorryAx','Lean.ofReduceBool','declaration uses `sorry`']),'forbidden trust leaf')
  for short in m['mandatory_axioms']:axioms(text,ns+'.'+short,m['kind']=='check')
  need(all(sha(p)==h for p,h in scientific.items()),'scientific definitions stable')
  return {'module':name,'source_sha256':m['sha256'],'object_sha256':r['object_sha256'],'receipt':str(folder/'RUN.json'),'receipt_sha256':sha(folder/'RUN.json'),'seconds':r['elapsed_seconds'],'kind':m['kind']}
 with ThreadPoolExecutor(max_workers=a.jobs)as pool:
  while pending or active:
   for name in sorted(pending):
    if not idle:break
    deps=set(mods[name]['dependencies'])&set(mods)
    if deps<=set(records):
     cpu=idle.pop(0);active[pool.submit(compile_one,name,cpu)]=(name,cpu);pending.remove(name)
   need(active,'complete acyclic exact module dependencies');done,_=wait(active,return_when=FIRST_COMPLETED)
   for future in done:
    name,cpu=active.pop(future);idle.append(cpu);records[name]=future.result();publish(out/'PROGRESS.json',{'status':'PARTIAL_NOT_ACCEPTANCE','completed':len(records),'total':len(mods),'last':name,'records':list(records.values())})
 need(set(records)==set(mods)and d['final_module']in records,'complete final consumer')
 # This independent controller source checks compulsory TYPES and AXIOMS, not
 # merely whatever print requests the untrusted proposer happened to include.
 cname='RamanujanPV.LocalWindowController_'+sha(mpath)[:16];croot=out/'controller-source';cpath=croot/Path(*cname.split('.')).with_suffix('.lean');cpath.parent.mkdir(parents=True)
 lines=['import '+d['final_module'],'open RamanujanPV','open QuotientDemandCheck','namespace '+cname];audit_names=[]
 for c in d['certificate_parameters']:
  n=c['p'];name=ns+'.prime_'+str(n);lines+=['example : Nat.Prime '+str(n)+' := '+name,'#print axioms '+name];audit_names.append((name,False))
 lines+=['example : LocalPrimeTree.PrimeTreeGood '+ns+'.primes := '+ns+'.primes_good','#print axioms '+ns+'.primes_good'];audit_names.append((ns+'.primes_good',False))
 for side,base,width in zip(['p','q'],d['bases'],d['widths']):
  for part,lo in enumerate(range(0,width,d['check_chunk'])):
   size=min(d['check_chunk'],width-lo);symbol=ns+'.part_'+side+'_'+str(part).zfill(4)
   lines+=['example : allFrom (PrimeWindow.checkEntry '+str(base)+' '+ns+'.primes '+ns+'.primeCount '+ns+'.'+side+'Entries) '+str(lo)+' '+str(size)+' = true := '+symbol,'#print axioms '+symbol];audit_names.append((symbol,True))
  symbol=ns+'.'+side+'_increment';lines+=['example (i : Nat) (hi : i < '+str(width)+') : Nat.primeCounting ('+str(base)+'+i+1) = Nat.primeCounting '+str(base)+' + ('+ns+'.'+side+'Entries.get i).cumulative := '+symbol+' i hi','#print axioms '+symbol];audit_names.append((symbol,False))
 for side,base,width,delta in zip(['p','q'],d['bases'],d['widths'],d['endpoint_deltas']):
  valueName=cname+'.'+side+'_last_value';countName=cname+'.'+side+'_endpoint'
  lines+=['theorem '+side+'_last_value : ('+ns+'.'+side+'Entries.get '+str(width-1)+').cumulative = '+str(delta)+' := by decide +kernel','#print axioms '+valueName]
  lines+=['theorem '+side+'_endpoint : Nat.primeCounting '+str(base+width)+' = Nat.primeCounting '+str(base)+' + '+str(delta)+' := by','  have h := '+ns+'.'+side+'_increment '+str(width-1)+' (by decide)','  simpa only ['+side+'_last_value] using h','#print axioms '+countName]
  audit_names.extend([(valueName,True),(countName,False)])
 lines+=['end '+cname]
 cpath.write_text('\n'.join(lines)+'\n');command=[sys.executable,str(S/'scripts/compile_lean.py'),cname,'--source-root',str(croot),'--audit-root',str(out/'controller-audit'),'--memory-gib',str(a.memory_gib),'--cpus',str(cpus[0])];r=subprocess.run(command,capture_output=True,text=True);(out/'controller.stdout').write_text(r.stdout);(out/'controller.stderr').write_text(r.stderr);need(r.returncode==0,'independent exact final type/axiom audit');folder=Path(json.loads(r.stdout.strip().splitlines()[-1])['audit']);text=(folder/'stdout').read_text()
 for name,numeric in audit_names:axioms(text,name,numeric)
 receipt={'status':'COMPLETED_HOST_LOCAL_KERNEL_INCREMENT_PROOFS_BASE_PAIR_PENDING_NOT_SOURCE_PV_ALONE','manifest':str(mpath),'manifest_sha256':sha(mpath),'widths':d['widths'],'bases':d['bases'],'endpoint_deltas':d['endpoint_deltas'],'actual_local_primes':d['actual_local_primes'],'all_certificate_primes':d['all_certificate_primes'],'scientific_sources':scientific,'seconds':time.monotonic()-start,'records':list(records.values()),'controller_source':str(cpath),'controller_source_sha256':sha(cpath),'controller_receipt':str(folder/'RUN.json'),'controller_receipt_sha256':sha(folder/'RUN.json'),'base_pair_closed_here':False,'full_finite_Ramanujan_claimed':False,'controller_sha256':sha(__file__)}
 publish(out/'RESULT.json',receipt);print(json.dumps({k:receipt[k]for k in ['status','widths','actual_local_primes','all_certificate_primes','seconds']},sort_keys=True))
if __name__=='__main__':main()
