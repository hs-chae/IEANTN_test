#!/usr/bin/env python3
from pathlib import Path
import json,hashlib,re,sys
S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1');R=Path('/data/ivy-ramanujan-source-pv-20261119/packed-mask-balanced-data-scout')
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
receipts=[]
for p in sorted(R.rglob('RUN.json')):
 d=read(p)
 if d.get('status')!='COMPILED':continue
 need(sha(d['source'])==d['source_sha256']==sha(p.parent/'source.lean'),'exactacceptedsource/snapshot');need(sha(d['command'][-1])==d['object_sha256'],'actualcurrentobject');
 for f,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(p.parent/f)==d[key],'actualacceptedlogs')
 text=(p.parent/'stdout').read_text();need('sorryAx'not in text and'Lean.ofReduceBool'not in text,'nonnative/admittedacceptedfacts');receipts.append(dict(module=d['module'],receipt=str(p),receipt_sha256=sha(p),source=d['source'],source_sha256=d['source_sha256'],object=d['command'][-1],object_sha256=d['object_sha256'],seconds=d['elapsed_seconds']))
by={x['module']:x for x in receipts};baseline=Path(by['RamanujanPV.PackedMaskDataEncoding.BaselineData']['source']).read_text();h=re.search(r'def value\s*:\s*Nat\s*:=\s*(0x[0-9a-fA-F]+)',baseline);need(h is not None,'independentliteraldata');expected=int(h.group(1),16)
old=Path('/data/ivy-ramanujan-source-pv-20261119/packed-sieve-mask-profile-v1/source/RamanujanPV/PackedSievePrimitiveMaskMillion.lean').read_text();oldh=re.search(r'def bits\s*:\s*Nat\s*:=\s*(0x[0-9a-fA-F]+)',old);need(oldh is not None and expected==int(oldh.group(1),16),'sameoriginalPinput')
variants=[]
for suffix,width in [('W256',256),('W1024',1024),('W4096',4096),('W4096DataOnly',4096)]:
 name='RamanujanPV.PackedMaskDataEncoding.'+suffix+'.Data';source=Path(by[name]['source']).read_text();expr=source.split('chunks : Lean.RArray Nat :=',1)[1].split('def value',1)[0];tokens=re.findall(r'0x[0-9a-fA-F]+|\.branch|\.leaf|\d+|[()]',expr);position=[0];checks=[]
 def tree():
  i=position[0];need(tokens[i]=='(','opening tree');position[0]+=1;kind=tokens[position[0]];position[0]+=1
  if kind=='.leaf':
   word=int(tokens[position[0]],0);position[0]+=1;need(tokens[position[0]]==')','leaf close');position[0]+=1;need(0<=word<2**width,'boundedword');return word,[word]
  need(kind=='.branch','exactconstructor');leftcount=int(tokens[position[0]]);position[0]+=1;left,lwords=tree();right,rwords=tree();need(tokens[position[0]]==')','branchclose');position[0]+=1;need(leftcount==len(lwords),'localleftleafcount');checks.append(leftcount);return left|(right<<(width*leftcount)),lwords+rwords
 value,words=tree();need(position[0]==len(tokens),'entire encodedtree consumed');need(value==expected,'allencodedbits equal originalP');need(len(words)==(1000000+width-1)//width,'exactwordpopulation');mask=2**width-1;need(all(w==((expected>>(i*width))&mask)for i,w in enumerate(words)),'everyoriginalword independently matched');variants.append(dict(namespace=suffix,width=width,words=len(words),branches=len(checks),value_bit_length=value.bit_length(),every_word_and_branch_checked=True,source_sha256=by[name]['source_sha256'],object_bytes=Path(by[name]['object']).stat().st_size))
provider=by['RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.ProviderCheck'];pt=Path(provider['source']).read_text();need(re.findall(r'^import (.+)$',pt,re.M)==['RamanujanPV.PackedSievePrimitiveBits','RamanujanPV.PackedMaskDataEncoding.W4096DataOnly.Data'],'standaloneproviderdirectimports');need('by decide +kernel'in pt,'actualkernelprovidercomputation');need('BaselineData'not in pt and 'Equality'not in pt,'no prior calibration dependence')
result=dict(status='PASS_BOUNDED_INDEPENDENT_ENCODING_SOURCE_WORD_LAYOUT_RECEIPT_REVIEW',reviewer_scope='AllcurrentlyCOMPILED scout receipts, four literal DATA representations, exact word/local-branch parity and standalone noncomputable4096 provider source. No new Lean replay launched by reviewer.',receipts=receipts,variants=variants,original_P_bits_independently_equal=True,codec=dict(source=str(S/'RamanujanPV/PackedMaskEncodingCodec.lean'),source_sha256=sha(S/'RamanujanPV/PackedMaskEncodingCodec.lean'),semantics='assemble uses stored branch value as LOCALleft-leaf count, not standardRArray.get globalpivot. Allactualbranches satisfy that localcount; .get is not used. The output scalar is independently kernel-calibrated and computedprovider-verified.',generic_theorems='assemble_leaf/assemble_branch are definitional/rfl; no arbitrary-tree concatenation claim assumed.'),provider=dict(module=provider['module'],seconds=provider['seconds'],source_sha256=provider['source_sha256'],receipt_sha256=provider['receipt_sha256'],not_C_source_PV=True),source_claims='Projectinternal Nat data codec and kernel mask computation, no external paper/Blueprint node claim. Exact original input equality is certified; native word readback is supplemental.',remaining='No new packed C program, physical loader/caller association or stronger ANT theorem is established by this representation-only scout.')
out=Path('/data/ivy-ramanujan-source-pv-20261119/prime-base-mask-scout-v1/ENCODING_INDEPENDENT_REVIEW.json');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status=result['status'],accepted_receipts=len(receipts),variants=len(variants),result_sha256=sha(out))))
