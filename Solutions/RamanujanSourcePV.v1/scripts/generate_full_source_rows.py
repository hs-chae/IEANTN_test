#!/usr/bin/env python3
"""Add source-execution proofs over immutable, already checked scalar records.
No old data/check/result is mutated; no prime-count truth is proposed here.
"""
from pathlib import Path
import argparse,hashlib,json,re
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--original-manifest',type=Path,required=True);p.add_argument('--original-result',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--name',required=True);p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');p.add_argument('--limit-blocks',type=int,default=0);p.add_argument('--allow-profile',action='store_true');a=p.parse_args()
 m=read(a.original_manifest);r=read(a.original_result);context=read(a.context)
 need(m['schema']=='RAMANUJAN_FULL_SCALARS_PROPOSAL_V1'and r['status']=='ALL_SCALAR_ENCLOSURE_AND_COVERAGE_KERNEL_CHECKS_PASS_COUNTS_OPEN_NOT_C_PV','accepted original scalar universe')
 need(r['manifest_sha256']==sha(a.original_manifest)and r['rows']==m['rows']and r['prime_counts_formally_proved_here']is False,'original result identity/scope')
 need(a.allow_profile or (m['rows']==1755663 and m['stop']==1490000000001 and m['full_locked_prefix']is True and a.limit_blocks==0),'full locked universe or explicit bounded control')
 need(0<=a.limit_blocks<=len(m['blocks'])and re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',a.name)is not None,'geometry/namespace')
 ns='RamanujanPV.'+a.name;need(ns!=m['namespace'],'separate original and additive namespaces')
 out=a.out.resolve();owned=Path(context['new_application_object_root']).resolve().parent;need(not out.exists()and out.is_relative_to(owned)and not out.is_relative_to(Path(m['source_root']).resolve()),'fresh experiment-owned additive output')
 for x in m['modules']:need(sha(x['source'])==x['source_sha256'],'immutable original written source '+x['module'])
 need(len(r['records'])==len(m['modules'])+1,'all original module receipts')
 for x,record in zip(m['modules'],r['records'][:-1]):
  receipt=Path(record['receipt']);rr=read(receipt);need(record['module']==x['module']and sha(receipt)==record['receipt_sha256']and rr['status']=='COMPILED'and rr['returncode']==0 and rr['source_sha256']==x['source_sha256'],'accepted original compile/source association')
 blocks=m['blocks'][:a.limit_blocks or len(m['blocks'])];out.mkdir(parents=True);src=out/'source';folder=src/'RamanujanPV'/a.name;folder.mkdir(parents=True);modules=[]
 header='/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/\n'
 for index,b in enumerate(blocks):
  old=b['namespace'];module=ns+'.Block'+format(index,'04d');path=folder/('Block'+format(index,'04d')+'.lean');text=header+'import RamanujanPV.FullFiniteSourcePV\nimport '+b['check_module']+'\nnamespace '+module+'\nopen QuotientDemandCheck FullFiniteScalars FullFiniteSourcePV\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\nnoncomputable def appCheck (i : Nat) : Bool := checkAppMargin ('+old+'.rows.get i).row 9005\n';parts=[]
  for part,offset in enumerate(range(0,b['count'],512)):
   count=min(512,b['count']-offset);label='part_'+format(part,'04d');union='union_'+format(part,'04d');text+='theorem '+label+' : allFrom appCheck '+str(offset)+' '+str(count)+'=true := by decide +kernel\n#print axioms '+label+'\n';text+='theorem '+union+' : allFrom appCheck 0 '+str(offset+count)+'=true := '+(label if part==0 else 'allFrom_append_checked (i:=0) (n:='+str(offset)+') (m:='+str(count)+') union_'+format(part-1,'04d')+' '+label)+'\n';parts.append(module+'.'+label)
  text+='theorem paired_checked : allFrom appCheck 0 '+old+'.count=true := union_'+format(len(parts)-1,'04d')+'\ntheorem certificate : SourceMarginCertificate '+old+'.start '+old+'.stop 9005 (rawRows '+old+'.rows '+old+'.count) := checked_block_source (by decide) '+old+'.checked paired_checked\n#print axioms paired_checked\n#print axioms certificate\nend '+module+'\n';path.write_text(text);modules.append(dict(module=module,source=str(path),source_sha256=sha(path),kind='block',dependencies=[],source_root=str(src),standard_constants=[*parts,module+'.paired_checked',module+'.certificate'],original_block=b))
 def expression(lo,hi,proof):
  if hi-lo==1:
   return modules[lo]['module']+'.certificate' if proof else '(FullFiniteScalars.rawRows '+blocks[lo]['namespace']+'.rows '+blocks[lo]['namespace']+'.count)'
  mid=(lo+hi)//2;left=expression(lo,mid,proof);right=expression(mid,hi,proof)
  return '(FullFiniteSourcePV.append_source_margin_certificate '+left+' '+right+')' if proof else '('+left+' ++ '+right+')'
 final=ns+'.Final';path=folder/'Final.lean';text=header+''.join('import '+x['module']+'\n'for x in modules)+'namespace '+ns+'\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\nnoncomputable def allRows : List RawFactoredCell := '+expression(0,len(blocks),False)+'\ntheorem all_source_margins : FullFiniteSourcePV.SourceMarginCertificate '+str(blocks[0]['start'])+' '+str(blocks[-1]['stop'])+' 9005 allRows := '+expression(0,len(blocks),True)+'\ntheorem all_source_scalars : FullFiniteSourcePV.SourceScalarCertificate '+str(blocks[0]['start'])+' '+str(blocks[-1]['stop'])+' allRows := all_source_margins.1\n#print axioms all_source_margins\n#print axioms all_source_scalars\nend '+ns+'\n';path.write_text(text);modules.append(dict(module=final,source=str(path),source_sha256=sha(path),kind='final',dependencies=[x['module']for x in modules],source_root=str(src),standard_constants=[ns+'.all_source_margins',ns+'.all_source_scalars']))
 result=dict(schema='RAMANUJAN_FULL_SOURCE_SCALARS_PROPOSAL_V1',status='UNTRUSTED_REQUIRES_ALL_ADDITIVE_KERNEL_SOURCE_EXECUTION_PROOFS',namespace=ns,source_root=str(src),modules=modules,rows=sum(b['count']for b in blocks),begin=blocks[0]['start'],stop=blocks[-1]['stop'],original_manifest=str(a.original_manifest.resolve()),original_manifest_sha256=sha(a.original_manifest),original_result=str(a.original_result.resolve()),original_result_sha256=sha(a.original_result),full_locked_prefix=m['full_locked_prefix']and len(blocks)==len(m['blocks']),additional_applicability='seven uint64 bounds;j<=n;Q<=j;P<=next-1;A=floor(n*eLo/Lu)',retained_integer_margin=9005,prime_counts_formally_proved_here=False,generator_sha256=sha(__file__),context_sha256=sha(a.context),final_module=final)
 (out/'PROPOSAL.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k]for k in ['status','rows','stop','full_locked_prefix','final_module']}))
if __name__=='__main__':main()
