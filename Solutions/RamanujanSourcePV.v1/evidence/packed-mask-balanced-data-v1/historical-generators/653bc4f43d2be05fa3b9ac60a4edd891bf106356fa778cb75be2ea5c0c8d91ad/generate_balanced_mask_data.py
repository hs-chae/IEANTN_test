#!/usr/bin/env python3
"""Generate three untrusted encodings of the same fixed proposed mask DATA."""
from pathlib import Path
import argparse,hashlib,json,re,time
PIN='2f6b880edf1b009758ccd4cac49644c299b02df3cfe52731e98c414dacc5775e'
def need(condition,message):
 if not condition:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--baseline-source',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 need(sha(a.baseline_source)==PIN,'exact accepted baseline source bytes required');out=a.out.resolve();need(not out.exists(),'fresh output required');src=out/'source';src.mkdir(parents=True)
 start=time.monotonic();text=a.baseline_source.read_text();literal=re.search(r'def bits : Nat := (0x[0-9a-f]+)',text).group(1);number=int(literal,16);count=1000000;records=[]
 def write(module,body,kind):
  path=src/Path(*module.split('.')).with_suffix('.lean');path.parent.mkdir(parents=True,exist_ok=True);path.write_text(body)
  records.append(dict(module=module,source=str(path),sha256=sha(path),bytes=path.stat().st_size,kind=kind))
 prefix='RamanujanPV.PackedMaskDataEncoding'
 write(prefix+'.BaselineData',f'import RamanujanPV.PackedMaskEncodingCodec\nnamespace {prefix}.BaselineData\ndef value : Nat := {literal}\nend {prefix}.BaselineData\n','baseline_data_only')
 for width in [256,1024,4096]:
  words=[(number>>offset)&((1<<width)-1)for offset in range(0,count,width)]
  def tree(xs):
   if len(xs)==1:return f'(.leaf {hex(xs[0])})'
   middle=len(xs)//2
   return f'(.branch {middle} {tree(xs[:middle])} {tree(xs[middle:])})'
  options='set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'if width==256 else''
  data=f'''import RamanujanPV.PackedMaskEncodingCodec
namespace {prefix}.W{width}
{options}def chunks : Lean.RArray Nat := {tree(words)}
def value : Nat := PackedMaskEncodingCodec.assemble {width} chunks
end {prefix}.W{width}
'''
  write(prefix+f'.W{width}.Data',data,'encoded_data_only')
  calibration=f'''import {prefix}.BaselineData
import {prefix}.W{width}.Data
namespace {prefix}.W{width}
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem data_equal : value={prefix}.BaselineData.value := by decide +kernel
#print axioms data_equal
end {prefix}.W{width}
'''
  write(prefix+f'.W{width}.Equality',calibration,'kernel_data_equality')
 manifest=dict(status='UNTRUSTED_DATA_PROPOSALS_UNTIL_KERNEL_EQUALITIES_COMPILE',width_bits=count,encoding_widths=[256,1024,4096],source_root=str(src),baseline_source=str(a.baseline_source.resolve()),baseline_source_sha256=PIN,baseline_packed_sha256=hashlib.sha256(number.to_bytes((count+7)//8,'little')).hexdigest(),records=records,generator_sha256=sha(__file__),generation_seconds=time.monotonic()-start,random_seed=None,scope='Same mask DATA only. Encoded providers import no baseline proof or baseline data; separate equality modules import baseline DATA for calibration. Not new packed C PV or new ANT result.')
 (out/'PROPOSAL.json').write_text(json.dumps(manifest,indent=2)+'\n');print(json.dumps(dict(modules=len(records),encoding_widths=manifest['encoding_widths'],data_sha256=manifest['baseline_packed_sha256'])))
if __name__=='__main__':main()
