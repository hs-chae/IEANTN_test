#!/usr/bin/env python3
"""Fresh proof-cost probe; preserves the entire original local classification."""
from pathlib import Path
import argparse
HEADER="/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n"
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 if a.out.exists():raise ValueError('fresh probe source')
 a.out.parent.mkdir(parents=True,exist_ok=True)
 t=HEADER+'import RamanujanPV.LocalWindowMillion.Data\nimport RamanujanPV.QuotientPartition\nnamespace RamanujanPV.LocalWindowSplitProbe\nopen LocalWindowMillion QuotientDemandCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 for group in ['p','q']:
  check=f'(PrimeWindow.checkEntry {group}Base primes primeCount {group}Entries)';names=[]
  for k in range(8):
   name=f'{group}6_piece_{k}';names.append(name);t+=f'theorem {name} : allFrom {check} {196608+k*4096} 4096=true := by decide +kernel\n#print axioms {name}\n'
  previous=names[0];length=4096
  for k,name in enumerate(names[1:],1):
   target=f'{group}6_range_{k}';t+=f'theorem {target} : allFrom {check} 196608 {length+4096}=true := QuotientPartition.append_checked (i:=196608) (n:={length}) (m:=4096) {previous} {name}\n';previous=target;length+=4096
  t+=f'theorem {group}6_complete : allFrom {check} 196608 32768=true := {previous}\n#print axioms {group}6_complete\n'
 t+='end RamanujanPV.LocalWindowSplitProbe\n';a.out.write_text(t);print(a.out)
if __name__=='__main__':main()
