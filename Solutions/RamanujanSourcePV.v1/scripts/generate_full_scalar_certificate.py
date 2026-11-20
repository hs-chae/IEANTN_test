#!/usr/bin/env python3
"""Untrusted exact proposal for EVERY original full-prefix scalar and adjacency.
No pi-count truth is supplied by these checks; numerical source PV is separate.
"""
from pathlib import Path
import argparse,hashlib,json,re,struct,time
HEADER='/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/\n'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--certificates',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--name',required=True);p.add_argument('--rows-per-block',type=int,default=4096);p.add_argument('--proof-chunk',type=int,default=512);p.add_argument('--limit-rows',type=int,default=0);a=p.parse_args();start=time.monotonic()
 d=read(a.run);need(d['status']=='UNTRUSTED_NUMERICAL_GENERATION_COMPLETE' and d['mode']=='actual' and d['begin']==38358837683 and d['end_inclusive']==1490000000000 and d['chunks']==64,'fixed original study');need([r['chunk'] for r in d['records']]==list(range(64)),'exact64 original chunks');need(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',a.name) is not None,'namespace');need(1<=a.proof_chunk<=a.rows_per_block<=8192 and a.limit_rows>=0,'bounded proof geometry')
 out=a.out.resolve();need(not out.exists(),'fresh proposal');out.mkdir(parents=True);source=out/'source';folder=source/'RamanujanPV'/a.name;folder.mkdir(parents=True);ns='RamanujanPV.'+a.name;modules=[];blocks=[];pending=[];total=0;expected=38358837683;inputs=[]
 def finish(path,module,kind,deps,**extra):modules.append(dict(module=module,source=str(path),source_sha256=sha(path),source_root=str(source),kind=kind,dependencies=deps,**extra))
 def emit(rows):
  index=len(blocks);bn=ns+'.Block'+format(index,'04d');name='Block'+format(index,'04d');dm=bn+'Data';cm=bn+'Check';dp=folder/(name+'Data.lean');cp=folder/(name+'Check.lean');lo=rows[0][0];hi=rows[-1][1];count=len(rows)
  def tree(i,j):
   if j-i==1:return '(.leaf ⟨⟨'+','.join(map(str,rows[i]))+'⟩,'+str(rows[i][0].bit_length()-1)+'⟩)'
   mid=(i+j)//2;return '(.branch '+str(mid)+' '+tree(i,mid)+' '+tree(mid,j)+')'
  dp.write_text(HEADER+'import RamanujanPV.FullFiniteScalars\nnamespace '+bn+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnoncomputable def rows : Lean.RArray FullFiniteScalars.Entry := '+tree(0,count)+'\ndef count : Nat := '+str(count)+'\ndef start : Nat := '+str(lo)+'\ndef stop : Nat := '+str(hi)+'\nnoncomputable def rowCheck : Nat → Bool := FullFiniteScalars.checkOne start stop count rows\nend '+bn+'\n');finish(dp,dm,'data',['RamanujanPV.FullFiniteScalars'])
  text=HEADER+'import '+dm+'\nnamespace '+bn+'\nopen QuotientDemandCheck FullFiniteScalars\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n';parts=[]
  for part,offset in enumerate(range(0,count,a.proof_chunk)):
   size=min(a.proof_chunk,count-offset);label='part_'+format(part,'04d');text+='theorem '+label+' : allFrom rowCheck '+str(offset)+' '+str(size)+'=true := by decide +kernel\n#print axioms '+label+'\n';union='union_'+format(part,'04d');text+='theorem '+union+' : allFrom rowCheck 0 '+str(offset+size)+'=true := '+(label if part==0 else 'allFrom_append_checked (i:=0) (n:='+str(offset)+') (m:='+str(size)+') union_'+format(part-1,'04d')+' '+label)+'\n';parts.append(label)
  text+='theorem checked : allFrom rowCheck 0 count=true := union_'+format(len(parts)-1,'04d')+'\ntheorem certificate : ScalarCertificate start stop (rawRows rows count) := checked_block (by decide) checked\n#print axioms checked\n#print axioms certificate\nend '+bn+'\n';cp.write_text(text);finish(cp,cm,'check',[dm],standard_constants=[bn+'.'+x for x in [*parts,'checked','certificate']]);blocks.append(dict(namespace=bn,start=lo,stop=hi,count=count,data_module=dm,check_module=cm))
 stopped=False
 for record in d['records']:
  file=a.certificates/(str(record['chunk'])+'.bin');need(file.stat().st_size==record['certificate_bytes'] and sha(file)==record['certificate_sha256'],'exact original binary identities');inputs.append(dict(chunk=record['chunk'],path=str(file.resolve()),bytes=file.stat().st_size,sha256=sha(file)));need(record['begin']==expected,'original chunk adjacency')
  count=0
  with file.open('rb') as f:
   for buf in iter(lambda:f.read(56*4096),b''):
    need(len(buf)%56==0,'complete exact seven-word records')
    for row in struct.iter_unpack('<7Q',buf):
     need(row[0]==expected and row[0]<row[1]<=record['end_exclusive'],'exact actual coverage');pending.append(row);total+=1;count+=1;expected=row[1]
     if len(pending)==a.rows_per_block:emit(pending);pending=[]
     if a.limit_rows and total==a.limit_rows:stopped=True;break
    if stopped:break
  if stopped:break
  need(count==record['numeric_result']['cells'] and expected==record['end_exclusive'],'every original row')
 if pending:emit(pending)
 need(total>0,'nonempty proposal')
 if not a.limit_rows:need(total==1755663 and expected==1490000000001,'entire locked full prefix')
 def expr(lo,hi,proof=False):
  if hi-lo==1:
   bn=blocks[lo]['namespace'];return bn+'.certificate' if proof else '(FullFiniteScalars.rawRows '+bn+'.rows '+bn+'.count)'
  mid=(lo+hi)//2
  if proof:return '(FullFiniteScalars.append_certificate '+expr(lo,mid,True)+' '+expr(mid,hi,True)+')'
  return '('+expr(lo,mid)+' ++ '+expr(mid,hi)+')'
 fm=ns+'.Final';fp=folder/'Final.lean';fp.write_text(HEADER+''.join('import '+b['check_module']+'\n' for b in blocks)+'namespace '+ns+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nnoncomputable def allRows : List RawFactoredCell := '+expr(0,len(blocks))+'\ntheorem all_scalars : FullFiniteScalars.ScalarCertificate 38358837683 '+str(expected)+' allRows := '+expr(0,len(blocks),True)+'\n#print axioms all_scalars\nend '+ns+'\n');finish(fp,fm,'final',[b['check_module'] for b in blocks],standard_constants=[ns+'.all_scalars'])
 result=dict(schema='RAMANUJAN_FULL_SCALARS_PROPOSAL_V1',status='UNTRUSTED_SCALAR_PROPOSAL_ALL_KERNEL_CHECKS_REQUIRED',namespace=ns,source_root=str(source),modules=modules,blocks=blocks,rows=total,begin=38358837683,stop=expected,limit_rows=a.limit_rows,full_locked_prefix=not bool(a.limit_rows),native_run_sha256=sha(a.run),native_binary_inputs=inputs,rows_per_block=a.rows_per_block,proof_chunk=a.proof_chunk,generator_sha256=sha(__file__),seconds=time.monotonic()-start,final_module=fm,prime_counts_formally_proved_here=False,source_first_PV=False)
 (out/'PROPOSAL.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','rows','stop','seconds','full_locked_prefix']}))
if __name__=='__main__':main()
