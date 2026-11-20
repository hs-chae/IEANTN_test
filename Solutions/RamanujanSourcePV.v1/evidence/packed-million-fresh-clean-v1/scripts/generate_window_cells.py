#!/usr/bin/env python3
"""Untrusted exact-integer local cell proposal; mandatory Lean checking follows."""
from pathlib import Path
import argparse,hashlib,json,math,re,time
from execute_local_prime_window import need,sha,read
S=Path(__file__).resolve().parents[1]
HEADER='/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/\n'
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--local-manifest',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--namespace',required=True);p.add_argument('--check-chunk',type=int,default=64);a=p.parse_args();started=time.monotonic()
 lp=a.local_manifest.resolve();d=read(lp);need(d['schema']=='RAMANUJAN_LOCAL_CLASSIFICATION_PROPOSAL_V1','local proposal schema');need(d['bases']==[38358837683,14111427770]and d['unchanged_base_values']==[1644673232,632207037],'owner base identities');need(1<=a.check_chunk<=256,'bounded exact row chunks');need(re.fullmatch(r'RamanujanPV\.[A-Za-z][A-Za-z0-9_]*',a.namespace)is not None,'namespace')
 for m in d['modules']:need(sha(m['source'])==m['sha256'],'classification source pin '+m['module'])
 entries=[]
 for side,width in zip('PQ',d['widths']):
  data=[]
  for m in sorted(d['modules'],key=lambda m:m['module']):
   if m['module'].split('.')[-1].startswith('Entries'+side):data.extend((x=='true',int(w),int(c))for x,w,c in re.findall(r'\(\.leaf ⟨(true|false),(\d+),(\d+)⟩\)',Path(m['source']).read_text()))
  need(len(data)==width,'all local entry leaves');entries.append(data)
 F=1<<60;scale=1<<20;elo=3133965575612453533;ehi=elo+22;N,J=d['bases'];P,Q=d['unchanged_base_values'];stop=N+d['widths'][0]+1
 def ceildiv(a,b):return(a+b-1)//b
 def logseries(a,b):
  z=ceildiv(F*a,b);z2=ceildiv(z*z,F);power=z;total=0
  for k in range(20):total+=ceildiv(power,2*k+1);power=ceildiv(power*z2,F)
  return 2*total+ceildiv(2*power*F,41*(F-z2))
 def logupper(n):return ceildiv(35*logseries(1,3)+logseries(n-(1<<35),n+(1<<35)),scale)
 primes=[N+i+1 for i,v in enumerate(entries[0])if v[0]];prefix=[[0]+[v[2]for v in data]for data in entries];n=N;idx=0;rows=[]
 while n<stop:
  lu=logupper(n);coefficient=n*elo//lu;j=n*F//ehi;need(J<=j<=J+d['widths'][1],'local q-query coverage');q=Q+prefix[1][j-J];allowed=math.isqrt((coefficient*q-1)//scale)
  while idx<len(primes)and P+idx<allowed:idx+=1
  nxt=min(primes[idx]if idx<len(primes)else stop,stop);pv=P+idx
  need(nxt>n and scale*pv*pv<coefficient*q,'strict actual target cell');need(pv==P+prefix[0][nxt-1-N],'actual p-count prefix')
  rows.append([n,nxt,j,pv,q,lu,coefficient]);n=nxt
 out=a.out.resolve();need(not out.exists(),'fresh proposal path');folder=out/'source'/Path(*a.namespace.split('.'));folder.mkdir(parents=True);ns=a.namespace;lns=d['namespace'];modules=[]
 def finish(path,name,kind,deps,names):modules.append({'module':name,'source':str(path),'sha256':sha(path),'kind':kind,'dependencies':deps,'mandatory_axioms':names})
 def tree(lo,hi):
  if hi-lo==1:return '(.leaf ⟨'+','.join(map(str,rows[lo]))+'⟩)'
  mid=(lo+hi)//2;return '(.branch '+str(mid)+' '+tree(lo,mid)+' '+tree(mid,hi)+')'
 data=folder/'Data.lean';dm=ns+'.Data';data.write_text(HEADER+'import RamanujanPV.WindowCells\nimport '+lns+'.Data\nnamespace '+ns+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnoncomputable def rows : Lean.RArray RamanujanPV.RawFactoredCell := '+tree(0,len(rows))+'\ndef rowCount : Nat := '+str(len(rows))+'\nnoncomputable def rowCheck : Nat → Bool := WindowCells.checkRow '+str(N)+' '+str(J)+' '+str(d['widths'][0])+' '+str(d['widths'][1])+' '+str(P)+' '+str(Q)+' '+str(stop)+' rowCount '+lns+'.pEntries '+lns+'.qEntries rows\nend '+ns+'\n');finish(data,dm,'data',[lns+'.Data'],[])
 parts=[]
 for part,lo in enumerate(range(0,len(rows),a.check_chunk)):
  count=min(a.check_chunk,len(rows)-lo);name='part_'+str(part).zfill(4);module=ns+'.Check'+str(part).zfill(4);path=folder/('Check'+str(part).zfill(4)+'.lean');path.write_text(HEADER+'import '+dm+'\nnamespace '+ns+'\nopen QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\ntheorem '+name+' : allFrom rowCheck '+str(lo)+' '+str(count)+'=true := by decide +kernel\n#print axioms '+name+'\nend '+ns+'\n');finish(path,module,'check',[dm],[name]);parts.append((lo,count,module,name))
 final=folder/'Final.lean';fm=ns+'.Final';text=HEADER+'import '+d['final_module']+'\n'+''.join('import '+part[2]+'\n'for part in parts)+'namespace '+ns+'\nopen QuotientDemandCheck QuotientCCell LocalPrimeTree\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 for k,(lo,count,module,name)in enumerate(parts):
  union='union_'+str(k).zfill(4);text+='theorem '+union+' : allFrom rowCheck 0 '+str(lo+count)+'=true := '+(name if k==0 else 'allFrom_append_checked (i:=0) (n:='+str(lo)+') (m:='+str(count)+') union_'+str(k-1).zfill(4)+' '+name)+'\n'
 args=' '.join(map(str,[N,J,*d['widths'],P,Q,stop,len(rows)]))+' '+lns+'.pEntries '+lns+'.qEntries rows'
 text+='theorem checked : WindowCells.checkRows '+args+'=true := by\n  exact congrArg (fun b=>true && b) union_'+str(len(parts)-1).zfill(4)+'\n'
 text+='theorem conditional_certificate (pRun : SourceExecution '+str(N)+' '+str(P)+') (qRun : SourceExecution '+str(J)+' '+str(Q)+') :\n    CompleteCertificate '+str(N)+' '+str(stop)+' ((WindowCells.rawList rows rowCount).map (fun r=>r.toCell WindowCells.eLo WindowCells.eHi)) :=\n  WindowCells.complete_certificate pRun qRun (bounded_prime_provider '+lns+'.primes_good '+lns+'.primeCount) '+lns+'.p_checked '+lns+'.q_checked checked\n'
 text+='theorem conditional_holds (pRun : SourceExecution '+str(N)+' '+str(P)+') (qRun : SourceExecution '+str(J)+' '+str(Q)+') :\n    ∀ x : ℝ, ('+str(N)+':ℝ) ≤ x → x < ('+str(stop)+':ℝ) → Holds x :=\n  complete_certificate_sound (conditional_certificate pRun qRun)\n'
 text+='#print axioms checked\n#print axioms conditional_certificate\n#print axioms conditional_holds\nend '+ns+'\n';final.write_text(text);finish(final,fm,'final',[d['final_module'],*[part[2]for part in parts]],['checked','conditional_certificate','conditional_holds'])
 manifest={'schema':'RAMANUJAN_LOCAL_REAL_CELLS_PROPOSAL_V1','status':'UNTRUSTED_REQUIRES_ALL_KERNEL_CHECKS_AND_SOURCE_BASE_PAIR','namespace':ns,'local_manifest':str(lp),'local_manifest_sha256':sha(lp),'local_final':d['final_module'],'source_root':str(out/'source'),'modules':modules,'final_module':fm,'bases':d['bases'],'widths':d['widths'],'unchanged_base_values':[P,Q],'stop':stop,'row_count':len(rows),'check_chunk':a.check_chunk,'rows':rows,'generator_sha256':sha(__file__),'seconds':time.monotonic()-started,'base_pair_closed_here':False,'full_finite_Ramanujan_claimed':False};(out/'PROPOSAL.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps({k:manifest[k]for k in ['status','widths','stop','row_count','seconds']}))
if __name__=='__main__':main()
