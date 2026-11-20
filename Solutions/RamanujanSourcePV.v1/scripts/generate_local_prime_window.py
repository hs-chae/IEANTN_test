#!/usr/bin/env python3
"""Untrusted local classification/Lucas certificate proposer; never mathematical acceptance.
The two base prime counts remain unchanged. Every local prime is proved in Lean;
every composite divisor and cumulative increment is checked by the kernel.
"""
from pathlib import Path
from collections import defaultdict
import argparse,hashlib,json,math,os,resource,time
S=Path(__file__).resolve().parents[1]
HEADER='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n'
N0=38358837683;J0=14111427770;P0=1644673232;Q0=632207037;F=1<<60;ELO=3133965575612453533

def need(value,message):
 if not value:raise ValueError(message)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--width',type=int,required=True);ap.add_argument('--name',required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--prime-chunk',type=int,default=128);ap.add_argument('--check-chunk',type=int,default=2048);ap.add_argument('--data-chunk',type=int,default=32768);a=ap.parse_args()
 need(56<=a.width<=1000000,'owner-authorized bounded width56..1e6');need(a.name.isascii()and a.name.isidentifier(),'exact simple Lean namespace');need(1<=a.prime_chunk<=1024 and 1<=a.check_chunk<=32768 and 1<=a.data_chunk<=131072,'bounded proposal chunks')
 out=a.out.resolve();need(not out.exists(),'fresh supplemental local proposal');out.mkdir(parents=True);started=time.monotonic();os.sched_setaffinity(0,{4,5,6,7});resource.setrlimit(resource.RLIMIT_AS,(64<<30,64<<30))
 widths=[a.width,((N0+a.width+1)*F)//ELO-J0];bases=[N0,J0];need(0<widths[1]<=a.width,'exact quotient-window range')
 root=math.isqrt(max(b+w for b,w in zip(bases,widths)));spf=list(range(root+1));small=[]
 for p in range(2,root+1):
  if spf[p]==p:
   small.append(p)
   for j in range(p*p,root+1,p):
    if spf[j]==j:spf[j]=p
 factors=[];target_primes=[]
 for base,width in zip(bases,widths):
  fac=[0]*width
  for p in small:
   first=max(p*p,((base+1+p-1)//p)*p)
   for n in range(first,base+width+1,p):
    k=n-base-1
    if not fac[k]:fac[k]=p
  factors.append(fac);target_primes.extend(base+i+1 for i,f in enumerate(fac)if not f)
 target_primes=sorted(set(target_primes));need(target_primes,'nonempty actual local prime population');certs={}
 def factorize(n):
  fs=[]
  for p in small:
   if p*p>n:break
   while n%p==0:fs.append(p);n//=p
  if n>1:fs.append(n)
  return fs
 def certificate(p):
  if p in certs:return
  if p<=100:
   certs[p]={'p':p,'small':True,'depth':0,'factors':[],'a':None};return
  fs=factorize(p-1);need(math.prod(fs)==p-1,'complete proposed factorization')
  for q in sorted(set(fs)):certificate(q)
  witness=None
  for x in range(2,100000):
   if pow(x,p-1,p)==1 and all(pow(x,(p-1)//q,p)!=1 for q in set(fs)):
    witness=x;break
  need(witness is not None,'bounded Lucas witness search; no numerical result accepted')
  certs[p]={'p':p,'small':False,'depth':1+max(certs[q]['depth']for q in fs),'factors':fs,'a':witness}
 for p in target_primes:certificate(p)
 source_root=out/'source';folder=source_root/'RamanujanPV'/a.name;folder.mkdir(parents=True);ns='RamanujanPV.'+a.name;modules=[];prime_module={};depths=defaultdict(list)
 for c in certs.values():depths[c['depth']].append(c['p'])
 def finish(path,module,kind,deps,required):
  modules.append({'module':module,'source':str(path),'source_root':str(source_root),'sha256':sha(path),'bytes':path.stat().st_size,'kind':kind,'dependencies':deps,'mandatory_axioms':required})
 for depth in sorted(depths):
  primes=sorted(depths[depth])
  for part,lo in enumerate(range(0,len(primes),a.prime_chunk)):
   batch=primes[lo:lo+a.prime_chunk];short=f'Primes{depth:02d}_{part:04d}';module=ns+'.'+short;path=folder/(short+'.lean');deps=sorted(set(prime_module[q]for p in batch for q in certs[p]['factors']))
   text=HEADER+'import RamanujanPV.LocalLucas\n'+''.join('import '+dep+'\n'for dep in deps)+'namespace '+ns+'\nopen LocalLucas\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n';required=[]
   for p in batch:
    c=certs[p];name='prime_'+str(p);required.append(name)
    text+=f'theorem {name} : Nat.Prime {p} := by\n'
    if c['small']:text+='  norm_num\n'
    else:
     fs=c['factors'];literal='['+','.join(map(str,fs))+']';patterns='|'.join('rfl'for _ in fs)
     text+=f'  apply prime_of_factorization {p} {c["a"]} {literal}\n  · decide +kernel\n  · intro q hq\n    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq\n'
     text+='    rcases hq with '+patterns+'\n'
     for q in fs:text+='    · exact prime_'+str(q)+'\n'
     text+='  · reduce_mod_char <;> norm_num\n  · intro q hq\n    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq\n'
     text+='    rcases hq with '+patterns+' <;> reduce_mod_char <;> norm_num <;> decide +kernel\n'
    text+='#print axioms '+name+'\n';prime_module[p]=module
   text+='end '+ns+'\n';path.write_text(text);finish(path,module,'prime',deps,required)
 def tree(lo,hi,leaf):
  need(lo<hi,'nonempty balanced tree')
  if hi-lo==1:return leaf(lo)
  mid=(lo+hi)//2;return '(.branch '+str(mid)+' '+tree(lo,mid,leaf)+' '+tree(mid,hi,leaf)+')'
 value_module=ns+'.PrimeValues';value_path=folder/'PrimeValues.lean';value_path.write_text(HEADER+'import Lean.Data.RArray\nnamespace '+ns+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnoncomputable def primes : Lean.RArray Nat := '+tree(0,len(target_primes),lambda i:'(.leaf '+str(target_primes[i])+')')+'\ndef primeCount : Nat := '+str(len(target_primes))+'\nend '+ns+'\n');finish(value_path,value_module,'data',[],[])
 proof_module=ns+'.PrimeProofs';proof_path=folder/'PrimeProofs.lean';deps=sorted(set(prime_module[p]for p in target_primes))
 def good(lo,hi):
  if hi-lo==1:return 'prime_'+str(target_primes[lo])
  mid=(lo+hi)//2;return '⟨'+good(lo,mid)+','+good(mid,hi)+'⟩'
 proof_path.write_text(HEADER+'import RamanujanPV.LocalPrimeTree\nimport '+value_module+'\n'+''.join('import '+dep+'\n'for dep in deps)+'namespace '+ns+'\nopen LocalPrimeTree\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\ntheorem primes_good : PrimeTreeGood primes := '+good(0,len(target_primes))+'\n#print axioms primes_good\nend '+ns+'\n');finish(proof_path,proof_module,'math',[value_module,*deps],['primes_good'])
 prime_index={p:i for i,p in enumerate(target_primes)};all_entries=[]
 for base,fac in zip(bases,factors):
  cumulative=0;rows=[]
  for i,f in enumerate(fac):
   n=base+i+1;prime=f==0;cumulative+=prime;rows.append((prime,prime_index[n]if prime else f,cumulative))
  all_entries.append(rows)
 data_module=ns+'.Data';data_path=folder/'Data.lean';data_parts=[]
 for side,base,width,rows in zip(['p','q'],bases,widths,all_entries):
  parts=[]
  for part,lo in enumerate(range(0,width,a.data_chunk)):
   hi=min(lo+a.data_chunk,width);short='Entries'+side.upper()+str(part).zfill(4);module=ns+'.'+short;path=folder/(short+'.lean');name=side+'Entries_'+str(part).zfill(4)
   literal=tree(lo,hi,lambda i:'(.leaf ⟨'+('true'if rows[i][0]else'false')+','+str(rows[i][1])+','+str(rows[i][2])+'⟩)')
   path.write_text(HEADER+'import RamanujanPV.LocalWindowCode\nnamespace '+ns+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnoncomputable def '+name+' : Lean.RArray PrimeWindow.Entry := '+literal+'\nend '+ns+'\n');finish(path,module,'data',[],[]);parts.append((lo,hi,module,name))
  data_parts.append(parts)
 text=HEADER+'import RamanujanPV.LocalWindowCode\nimport '+value_module+'\n'+''.join('import '+p[2]+'\n'for parts in data_parts for p in parts)+'namespace '+ns+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 for side,base,width,parts in zip(['p','q'],bases,widths,data_parts):
  def merged(lo,hi):
   if hi-lo==1:return parts[lo][3]
   mid=(lo+hi)//2;return '(.branch '+str(parts[mid][0])+' '+merged(lo,mid)+' '+merged(mid,hi)+')'
  text+=f'def {side}Base : Nat := {base}\ndef {side}Count : Nat := {width}\nnoncomputable def {side}Entries : Lean.RArray PrimeWindow.Entry := '+merged(0,len(parts))+'\n'
 text+='end '+ns+'\n';data_path.write_text(text);finish(data_path,data_module,'data',[value_module,*[p[2]for parts in data_parts for p in parts]],[])
 checks=[]
 for side,width in zip(['p','q'],widths):
  parts=[]
  for part,lo in enumerate(range(0,width,a.check_chunk)):
   size=min(a.check_chunk,width-lo);short='Check'+side.upper()+str(part).zfill(4);module=ns+'.'+short;path=folder/(short+'.lean');name='part_'+side+'_'+str(part).zfill(4)
   path.write_text(HEADER+'import '+data_module+'\nnamespace '+ns+'\nopen QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\ntheorem '+name+' : allFrom (PrimeWindow.checkEntry '+side+'Base primes primeCount '+side+'Entries) '+str(lo)+' '+str(size)+'=true := by decide +kernel\n#print axioms '+name+'\nend '+ns+'\n');finish(path,module,'check',[data_module],[name]);parts.append((lo,size,module,name))
  checks.append(parts)
 final_module=ns+'.Final';final_path=folder/'Final.lean';text=HEADER+'import RamanujanPV.PrimeWindow\nimport '+proof_module+'\n'+''.join('import '+part[2]+'\n'for parts in checks for part in parts)+'namespace '+ns+'\nopen QuotientDemandCheck PrimeWindow LocalPrimeTree\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n';required=[]
 for side,width,base,parts in zip(['p','q'],widths,bases,checks):
  for j,(lo,size,module,name)in enumerate(parts):
   union='union_'+side+'_'+str(j).zfill(4)
   text+='theorem '+union+' : allFrom (PrimeWindow.checkEntry '+side+'Base primes primeCount '+side+'Entries) 0 '+str(lo+size)+'=true := '
   text+=name+'\n'if j==0 else f'allFrom_append_checked (i:=0) (n:={lo}) (m:={size}) union_{side}_{j-1:04d} {name}\n'
  text+=f'theorem {side}_checked : PrimeWindow.checkAll {side}Base primes primeCount {side}Entries {side}Count=true := union_{side}_{len(parts)-1:04d}\n'
  text+=f'theorem {side}_increment (i : Nat) (hi : i < {width}) :\n    Nat.primeCounting ({base}+i+1)=Nat.primeCounting {base}+({side}Entries.get i).cumulative :=\n  PrimeWindow.count_at (bounded_prime_provider primes_good primeCount) {side}_checked hi\n#print axioms {side}_increment\n';required.append(side+'_increment')
 text+='end '+ns+'\n';final_path.write_text(text);finish(final_path,final_module,'final',[proof_module,*[p[2]for parts in checks for p in parts]],required)
 manifest={'schema':'RAMANUJAN_LOCAL_CLASSIFICATION_PROPOSAL_V1','status':'UNTRUSTED_PROPOSAL_REQUIRES_ALL_KERNEL_PROOFS','namespace':ns,'bases':bases,'unchanged_base_values':[P0,Q0],'widths':widths,'actual_local_primes':len(target_primes),'all_certificate_primes':len(certs),'max_certificate_depth':max(depths),'certificate_parameters':sorted(certs.values(),key=lambda c:c['p']),'endpoint_deltas':[rows[-1][2]for rows in all_entries],'source_root':str(source_root),'modules':modules,'final_module':final_module,'generator_sha256':sha(__file__),'prime_chunk':a.prime_chunk,'check_chunk':a.check_chunk,'data_chunk':a.data_chunk,'seconds':time.monotonic()-started,'peak_RSS_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024,'seed':None,'qualification':'Ordinary kernel local prime/composite and count-increment certificates. Source-first C program proof and base numerical proofs remain separate, explicitly consumed dependencies. This is not an accepted result until every source module and final mathematical consumer compiles and is independently audited.'}
 (out/'PROPOSAL.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k]for k in ['status','widths','actual_local_primes','all_certificate_primes','max_certificate_depth','endpoint_deltas','seconds','peak_RSS_bytes']},sort_keys=True))
if __name__=='__main__':main()
