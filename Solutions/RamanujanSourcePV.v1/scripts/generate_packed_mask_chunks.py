#!/usr/bin/env python3
"""Untrusted proposals for exact OR-fold partition proofs. No PV claim."""
from pathlib import Path
import argparse,bisect,hashlib,json,math,re,time
S=Path(__file__).resolve().parents[1]
BASELINE_SHA='2f6b880edf1b009758ccd4cac49644c299b02df3cfe52731e98c414dacc5775e'
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def packed(flags):
 out=bytearray((len(flags)+7)//8)
 for i,x in enumerate(flags):
  if x:out[i//8]|=1<<(i%8)
 return int.from_bytes(out,'little')
def main():
 parser=argparse.ArgumentParser(allow_abbrev=False)
 parser.add_argument('--out',type=Path,required=True);parser.add_argument('--baseline-source',type=Path,required=True)
 parser.add_argument('--control',action='store_true');args=parser.parse_args();root=args.out.resolve()
 need(not root.exists(),'fresh output required');need(sha(args.baseline_source)==BASELINE_SHA,'exact accepted baseline source required')
 text=args.baseline_source.read_text();baseline=int(re.search(r'def bits : Nat := (0x[0-9a-f]+)',text).group(1),16)
 lo,count=(2,999)if args.control else(38358837684,1000000)
 hi=lo+count-1;r=math.isqrt(hi);total=r-1;ks=[2]if args.control else[1,2,8,16]
 begin=time.monotonic();prime=bytearray(b'\1')*(r+1);prime[:2]=b'\0\0'
 for p in range(2,math.isqrt(r)+1):
  if prime[p]:prime[p*p:r+1:p]=b'\0'*(((r-p*p)//p)+1)
 base=packed([not prime[n]for n in range(2,r+1)])
 bounds={k:[total*i//k for i in range(k+1)]for k in ks}
 masks={k:[bytearray(count)for _ in range(k)]for k in ks}
 for p in range(2,r+1):
  if not prime[p]:continue
  j=p-2;first=max(p*p,((lo+p-1)//p)*p)
  if first>hi:continue
  ones=b'\1'*((hi-first)//p+1)
  for k in ks:
   index=bisect.bisect_right(bounds[k],j)-1
   masks[k][index][first-lo:count:p]=ones
 values={k:[packed(a)for a in arrays]for k,arrays in masks.items()}
 all_composites=0
 for value in values[ks[0]]:all_composites|=value
 expected=((1<<count)-1)^(((1<<count)-1)&all_composites)
 if not args.control:need(expected==baseline,'native proposal differs from accepted original mask')
 prefix='RamanujanPV.PackedMaskChunkControl'if args.control else'RamanujanPV.PackedMaskChunkPilot'
 src=root/'source';records=[]
 def write(module,body,kind):
  p=src/Path(*module.split('.')).with_suffix('.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(body)
  records.append(dict(module=module,source=str(p),sha256=sha(p),bytes=p.stat().st_size,kind=kind))
 common=f'''import RamanujanPV.PackedMaskChunks
namespace {prefix}
open PackedSieveKernel PackedMaskChunks
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
def base : Nat := {hex(base)}
def expected : Nat := {hex(expected)}
def baselineValue : Nat := {hex(expected if args.control else baseline)}
theorem expected_value : expected=baselineValue := by decide +kernel
theorem base_checked : allMask 2 {r}=base := by decide +kernel
#print axioms expected_value
#print axioms base_checked
end {prefix}
'''
 write(prefix+'.Common',common,'shared_base')
 for k in ks:
  lengths=[bounds[k][i+1]-bounds[k][i]for i in range(k)]
  data=f'import {prefix}.Common\nnamespace {prefix}.K{k}\n'
  data+='def lengths : List Nat := ['+','.join(map(str,lengths))+']\n'
  for i,value in enumerate(values[k]):data+=f'def value{i} : Nat := {hex(value)}\n'
  data+=f'end {prefix}.K{k}\n';write(prefix+f'.K{k}.Data',data,'data')
  for i,length in enumerate(lengths):
   start=bounds[k][i]
   leaf=f'''import {prefix}.K{k}.Data
namespace {prefix}.K{k}
open PackedMaskChunks
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem chunk{i} : rangeMask {lo} {hi} {prefix}.base {start} {length}=value{i} := by decide +kernel
#print axioms chunk{i}
end {prefix}.K{k}
'''
   write(prefix+f'.K{k}.Check{i:04d}',leaf,'chunk')
  final=''.join(f'import {prefix}.K{k}.Check{i:04d}\n'for i in range(k))
  final+=f'namespace {prefix}.K{k}\nopen PackedSieveKernel PackedSievePrimitiveBits PackedMaskChunks\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
  final+=f'''theorem composite_value : compositeMask {lo} {count}=
      combine {lo} {hi} {prefix}.base 0 lengths := by
  have h:=composite_from_chunks {lo} {count} lengths (by decide +kernel)
  rw [show {lo}+{count}-1={hi} by decide,show Nat.sqrt {hi}={r} by decide +kernel,{prefix}.base_checked] at h
  exact h
'''
  expr='0'
  for i in reversed(range(k)):expr=f'(value{i} ||| {expr})'
  final+=f'''theorem chunks_joined : combine {lo} {hi} {prefix}.base 0 lengths={expr} := by
  simp only [combine,lengths]
  rw [{','.join(f'chunk{i}'for i in range(k))}]
'''
  final+=f'''theorem finish_numeric : (twoPow {count}-1) ^^^ ((twoPow {count}-1) &&& {expr})={prefix}.expected := by decide +kernel

theorem same_original_mask : primeBits {lo} {count}={prefix}.expected := by
  rw [←primitiveBits_eq]
  unfold primitiveBits
  rw [composite_value,chunks_joined]
  exact finish_numeric
#print axioms composite_value
#print axioms chunks_joined
#print axioms finish_numeric
#print axioms same_original_mask
end {prefix}.K{k}
'''
  write(prefix+f'.K{k}.Final',final,'final')
 manifest=dict(status='UNTRUSTED_PROPOSAL_NO_PROOF_ACCEPTANCE',control_only=args.control,lo=lo,count=count,hi=hi,r=r,total_j=total,partitions=ks,boundaries=bounds,baseline_source=str(args.baseline_source.resolve()),baseline_sha256=BASELINE_SHA,generator_sha256=sha(__file__),source_root=str(src),records=records,expected_packed_sha256=hashlib.sha256(expected.to_bytes((count+7)//8,'little')).hexdigest(),random_seed=None,generation_seconds=time.monotonic()-begin)
 (root/'PROPOSAL.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(dict(status=manifest['status'],modules=len(records),lo=lo,count=count,partitions=ks)))
if __name__=='__main__':main()
