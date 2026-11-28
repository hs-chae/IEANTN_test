#!/usr/bin/env python3
"""Untrusted, deterministic W4 integer-FFT trace proposal. Lean checks every step.
Zero subtrees are omitted only where the generic sparse-input theorem applies.
This producer, native agreement, and kernel certificates are not source-first PV.
"""
from pathlib import Path
from hashlib import sha256
import argparse,json,time
R=Path(__file__).resolve().parents[3]
a=argparse.ArgumentParser(allow_abbrev=False);a.add_argument('--stages',type=int,required=True);a.add_argument('--out',type=Path,required=True);a.add_argument('--chunk-log',type=int,default=13);a.add_argument('--pairs-per-module',type=int,default=524288);o=a.parse_args()
if not 13<=o.stages<=24 or not 4<=o.chunk_log<=16:raise ValueError('Supported W4 grid/chunk')
if o.pairs_per_module<2**(o.chunk_log+1) or o.out.exists():raise ValueError('Fresh output and sufficient grouping required')
source=R/'Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs/w4.json';raw=source.read_bytes()
if sha256(raw).hexdigest()!='61f745f27018ea5addbb01c1d583b128b2639b0f101d764136c98c26983c5521':raise ValueError('Original W4 bytes changed')
d=json.loads(raw)
if d['m']!=360 or d['scale']!=10**16 or len(d['coefficients'])!=2520 or any(type(v)is not int for v in d['coefficients']):raise ValueError('Locked W4 profile')
o.out.mkdir();started=time.monotonic();S=o.stages;N=2**S;K=2**o.chunk_log;U=10**36;PI=3141592653589793238462643383279502884;NS=f'W4DAG{S}';P=f'W4D{S}';coeff=d['coefficients'];modules={};payloads=[];groups={};node_count=zero_count=checks=0
header='set_option autoImplicit false\nset_option Elab.async false\nset_option maxRecDepth 2000000\nset_option maxHeartbeats 0\nnoncomputable section\n'
def integer(n):return f'(Int.ofNat {n})' if n>=0 else f'(Int.negSucc {-n-1})'
def pair(z):return f'({integer(z[0])},{integer(z[1])})'
def mul(a,b):return(a[0]*b[0]//U-a[1]*b[1]//U,a[0]*b[1]//U+a[1]*b[0]//U)
def add(a,b):return(a[0]+b[0],a[1]+b[1])
def sub(a,b):return(a[0]-b[0],a[1]-b[1])
def ceil(a,b):return(a+b-1)//b
def root(n):
 x=2*PI//n;x2=x*x//U;ct=cr=U;st=sr=x
 for i in range(1,11):
  ct=(ct*x2//U)//(2*i*(2*i-1));st=(st*x2//U)//(2*i*(2*i+1));cr+=(-1 if i%2 else 1)*ct;sr+=(-1 if i%2 else 1)*st
 return(cr,-sr)
def balanced(items,op='++'):
 if not items:return'[]'
 if len(items)==1:return items[0]
 m=len(items)//2;left=balanced(items[:m],op);right=balanced(items[m:],op)
 return f'({left} ++ {right})' if op=='++' else f'({op} {left} {right})'
def write_module(name,imports,body):
 text=''.join(f'import {v}\n'for v in sorted(set(imports)))+header+f'namespace {NS}\nopen RH080Next.FFT.IntegerModel\n'+body+f'\nend {NS}\n';p=o.out/(name+'.lean');p.write_text(text);modules[name]={'file':p.name,'imports':sorted(set(imports)),'sha256':sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
class Group:
 def __init__(self,name,width,table=True):
  self.name=name;self.width=width;self.rows=0;self.body=[];self.imports={P+'Tables' if table else P+'Base'};self.path=o.out/(name+'.csv');self.stream=None;groups[name]=self
 def rows_add(self,a,b=None):
  if self.stream is None:self.stream=self.path.open('x')
  index=self.rows
  for values in [a]if b is None else[a,b]:
   if len(values)!=self.width:raise ValueError('Wrong rectangular data width')
   self.stream.write(''.join(f'{x},{y}\n'for x,y in values));self.rows+=1
  return index
 def ref(self,name):return self.name+'.'+name
 def getter(self,name,row):
  self.body.append(f'def {name} : List CInt := numbers.getD {row} []\n');return self.ref(name)
 def finish(self):
  body=f'namespace {self.name}\n'
  if self.stream is not None:
   self.stream.close();body+=f'forest_certificate numbers from "{self.path.name}" width {self.width} rows {self.rows}\n';payloads.append({'file':self.path.name,'bytes':self.path.stat().st_size,'sha256':sha256(self.path.read_bytes()).hexdigest()})
  body+=''.join(self.body)+f'end {self.name}\n';write_module(self.name,self.imports,body)
seed=root(N);tw=[(U,0)]
for _ in range(N//2-1):tw.append(mul(tw[-1],seed))
write_module(P+'Base',['W4FFTPairedIntModel','FFTUntrustedData'],f'def seed : CInt := {pair(seed)}\ndef actualInput (j : Nat) : CInt := RH080Next.FFT.IntegerModel.W4.input {N} j\n')
ws={};wrefs={};wmods={};wlens={};segment_refs=[];segment_lists=[]
for s in range(1,S+1):
 half=2**(s-1);stride=N//2**s;values=[tw[j*stride]for j in range(half)];width=min(half,K);refs=[];mods=[];lens=[]
 for b in range((half+K-1)//K):
  name=f'{P}W{s:02}G{b//32}';g=groups.get(name)or Group(name,width,False);row=g.rows_add(values[b*K:(b+1)*K]);ref=g.getter(f'w{b}',row);refs.append(ref);mods.append(g.name);ln=g.ref(f'length_w{b}');lens.append(ln);g.body.append(f'theorem length_w{b} : w{b}.length={width} := by decide +kernel\n')
  if s==S:
   entries=ref+'.tail' if b==0 else ref;previous=(U,0)if b==0 else values[b*K-1];final=values[min((b+1)*K,half)-1];sn=g.ref(f'segment{b}');g.body.append(f'theorem segment{b} : TwiddleSegment seed {pair(previous)} ({entries}) {pair(final)} := checkTwiddleSegment_sound _ _ _ _ (by decide +kernel)\n');segment_refs.append(sn);segment_lists.append(entries)
 ws[s]=values;wrefs[s]=refs;wmods[s]=mods;wlens[s]=lens
# Freeze only WS groups first; node groups are accumulated subsequently.
for g in list(groups.values()):g.finish()
ws_groups=set(groups);tables=''
for s in range(1,S+1):
 tables+=f'def w{s:02} : List CInt := {balanced(wrefs[s])}\ntheorem length_w{s:02} : w{s:02}.length={2**(s-1)} := by\n  unfold w{s:02}\n  simp only [List.length_append,'+','.join(wlens[s])+']\n  all_goals decide +kernel\n'
tables+='def stages : Nat → List CInt\n  | 0 => []\n'+''.join(f'  | {s} => w{s:02}\n'for s in range(1,S+1))+'  | _ => []\n'
tables+=f'theorem stage_lengths : ∀ t<{S}, (stages (t+1)).length=2^t := by\n  intro t ht\n  interval_cases t\n'+''.join(f'  · exact length_w{s:02}\n'for s in range(1,S+1))
write_module(P+'Tables',[P+'Base',*set(m for refs in wmods.values()for m in refs)],tables)
# Exact decimations, checked in bounded blocks, then mathematically composed.
dec_refs={};dec_modules=[]
for s in range(1,S):
 proofs=[]
 for b,low in enumerate(wrefs[s]):
  name=f'{P}E{s:02}G{b//32}';g=groups.get(name)
  if g is None:g=Group(name,0,False)
  # These modules have no new data; use the immutable WS definitions.
  high=wrefs[s+1][0]if len(wrefs[s+1])==1 else balanced(wrefs[s+1][2*b:2*b+2]);highermods=wmods[s+1][:1]if len(wrefs[s+1])==1 else wmods[s+1][2*b:2*b+2];g.imports.update([wmods[s][b],*highermods]);lns=wlens[s+1][:1]if len(wrefs[s+1])==1 else wlens[s+1][2*b:2*b+2]
  g.body.append(f'theorem block{b} : EvenBlock ({high}) {low} := by\n  constructor\n  · exact checkEvens_sound _ _ (by decide +kernel)\n  · simp only [List.length_append,'+','.join(lns)+']\n    all_goals decide +kernel\n');proofs.append(g.ref(f'block{b}'))
 dec_refs[s]=proofs
for name,g in list(groups.items()):
 if name not in ws_groups:g.finish();dec_modules.append(name)
fixed_groups=set(groups)
# Native recursive proposal, retaining only the current recursion path's values.
root_sums=[]
def node(level,index,step):
 global node_count,zero_count,checks
 if 2520<=index and index+2520<=step:
  zero_count+=1;out=f'(List.replicate {2**level} (0,0))';proof=f'(sparse_zero_execution stages 2520 {N} {level} {index} {step} RH080Next.FFT.IntegerModel.W4.coefficient (fun t ht => stage_lengths t (by omega)) (by decide +kernel) (by decide +kernel) (by decide +kernel))'
  return {'out':out,'proof':proof,'refs':[out],'module':None},[(0,0)]*(2**level)
 if level==0:
  k=index if index<2520 else N-index;v=(coeff[k]*10**20,0)if k<2520 else(0,0);out=f'[actualInput {index}]'
  return {'out':out,'proof':f'(ExecutionTrace.leaf (stages := stages) (input := actualInput) {index} {step})','refs':[out],'module':None},[v]
 left,av=node(level-1,index,step*2);right,bv=node(level-1,index+step,step*2);half=2**(level-1);length=2*half;chunk_width=min(half,K);num_chunks=(half+K-1)//K;group_nodes=min(128,max(1,o.pairs_per_module//length));base=f'{P}N{level:02}G{index//group_nodes}';large=length>o.pairs_per_module;g=None if large else(groups.get(base)or Group(base,chunk_width));prefs=[];qrefs=[];merges=[];pvalues=[];qvalues=[];chunkmods=[]
 for b in range(num_chunks):
  if large:
   per=max(1,o.pairs_per_module//(2*K));gn=f'{P}B{level:02}I{index}G{b//per}';cg=groups.get(gn)or Group(gn,chunk_width)
  else:cg=g
  for child in [left,right]:
   if child['module']:cg.imports.add(child['module'])
  cg.imports.add(wmods[level][b]);lo=b*K;hi=min(lo+K,half);pv=[];qv=[]
  for j in range(lo,hi):
   product=mul(bv[j],ws[level][j]);pv.append(add(av[j],product));qv.append(sub(av[j],product))
  row=cg.rows_add(pv,qv);pname=f'p{level}_{index}_{b}';qname=f'q{level}_{index}_{b}';pr=cg.getter(pname,row);qr=cg.getter(qname,row+1);prefs.append(pr);qrefs.append(qr);ar=left['refs'][b];br=right['refs'][b];wr=wrefs[level][b];mr=cg.ref(f'm{level}_{index}_{b}')
  cg.body.append(f'theorem m{level}_{index}_{b} : MergeTrace ({ar}) ({br}) {wr} {pname} {qname} := checkMerge_sound _ _ _ _ _ (by decide +kernel)\n');merges.append(mr);checks+=hi-lo;pvalues.extend(pv);qvalues.extend(qv);chunkmods.append(cg.name)
  if level==S:
   for ref,name,values in [(pr,pname,pv),(qr,qname,qv)]:
    total=sum(abs(x)for x,y in values);sn=cg.ref(name+'_sum');cg.body.append(f'theorem {name}_sum : absSum {name}={total} := by decide +kernel\n');root_sums.append((ref,sn,total))
 if large:
  g=Group(base,0);g.imports.update(chunkmods)
 for child in [left,right]:
  if child['module']:g.imports.add(child['module'])
 pexpr=balanced(prefs);qexpr=balanced(qrefs);outname=f'o{level}_{index}';outref=g.ref(outname);tr=g.ref(f'exec{level}_{index}');g.body.append(f'def {outname} : List CInt := {pexpr} ++ {qexpr}\ntheorem exec{level}_{index} : ExecutionTrace stages actualInput {level} {index} {step} {outname} :=\n  ExecutionTrace.node {level-1} {index} {step} ({left["out"]}) ({right["out"]}) ({pexpr}) ({qexpr}) {left["proof"]} {right["proof"]} {balanced(merges,"MergeTrace.append")}\n');node_count+=1
 return {'out':outref,'proof':tr,'refs':[outref]if length<=K else prefs+qrefs,'module':g.name},pvalues+qvalues
meta,values=node(S,0,1)
for name,g in list(groups.items()):
 if name not in fixed_groups:g.finish()
total=sum(abs(x)for x,y in values);quad=sum(20*j*j*abs(v)for j,v in enumerate(coeff));numerator=ceil(ceil(ceil(total,10**18),100),N)+ceil(ceil(ceil(quad,3),N),N)+100
if S==24 and numerator!=7813568381279800:raise ValueError('Different actual C native crosscheck')
body=f'def output : List CInt := {meta["out"]}\ntheorem complete_execution : ExecutionTrace stages actualInput {S} 0 1 output := {meta["proof"]}\ndef topTail : List CInt := {balanced(segment_lists)}\ntheorem top_shape : w{S:02}=(unit,0)::topTail := by\n  have hh : {wrefs[S][0]}=(unit,0)::{wrefs[S][0]}.tail := by rfl\n  unfold w{S:02} topTail\n  rw [hh]\n  simp only [List.cons_append,List.tail_cons]\ntheorem global_twiddle_trace : TwiddleTrace seed (unit,0) w{S:02}.tail := by\n  rw [top_shape]\n  exact TwiddleSegment.forget_final {balanced(segment_refs,"TwiddleSegment.append")}\n'
for s in range(1,S):body+=f'theorem decimation{s:02} : EvenTrace w{s+1:02} w{s:02} := EvenBlock.trace {balanced(dec_refs[s],"EvenBlock.append")}\n'
body+=f'theorem total_checked : absSum output={total} := by\n  unfold output {meta["out"]}\n  simp only [absSum_append,'+','.join(p[1]for p in root_sums)+']\n  all_goals decide +kernel\n'
body+=f'theorem quad_checked : RH080Next.FFT.IntegerModel.W4.quad={quad} := by decide +kernel\ntheorem numerator_checked : RH080Next.FFT.IntegerModel.W4.normFromOutput {N} output={numerator} := by\n  unfold RH080Next.FFT.IntegerModel.W4.normFromOutput\n  rw [fold_absSum,Nat.zero_add,total_checked,quad_checked]\n  all_goals decide +kernel\n#print axioms complete_execution\n#print axioms global_twiddle_trace\n#print axioms numerator_checked\n'+''.join(f'#print axioms decimation{s:02}\n'for s in range(1,S))
write_module(P+'Final',[P+'Tables',meta['module'],*dec_modules],body)
plan={'status':'UNTRUSTED_W4_DAG_PROPOSAL_NOT_PROOF_NOT_PV','stages':S,'n':N,'chunk':K,'pairs_per_module':o.pairs_per_module,'namespace':NS,'final_module':P+'Final','input_sha256':sha256(raw).hexdigest(),'source_input':str(source),'producer_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'seed':seed,'total_abs':total,'quad':quad,'norm_numerator':numerator,'nonzero_nodes':node_count,'zero_subtrees':zero_count,'butterflies_checked':checks,'modules':list(modules.values()),'payloads':payloads,'producer_seconds':time.monotonic()-started}
(o.out/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n');print(json.dumps({k:plan[k]for k in ['status','stages','norm_numerator','nonzero_nodes','zero_subtrees','butterflies_checked','producer_seconds']}),flush=True)
