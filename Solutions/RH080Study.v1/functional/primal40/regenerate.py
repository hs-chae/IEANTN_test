#!/usr/bin/env python3
"""Regenerate all exact degree80 input coefficients and 1193 kernel-checkable cells.

No numerical generation result is a Lean acceptance receipt. This program checks
byte equality with the frozen, independently compiled source manifest. Standard
library only; no randomness. Use a fresh experiment-owned --out directory.
"""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,subprocess,sys,time
from generate_kernel_cells import source_polynomials,llist

HEADER='''/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
'''

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,msg):
 if not c:raise ValueError(msg)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
 here=Path(__file__).resolve().parent;out=args.out.resolve()
 require(not out.exists(),'--out must be a fresh directory')
 require(out!=here and here not in out.parents,'scratch must be outside publishable source')
 out.mkdir(parents=True);start=time.monotonic()
 candidate=here/'CANDIDATE_LAGUERRE40.json';partition=here/'PARTITION.json'
 exact=json.loads((here/'COEFFICIENTS_EXACT.json').read_text());manifest=json.loads((here/'CELL_SOURCE_MANIFEST.json').read_text())
 require(sha(candidate)==exact['candidate_sha256'],'candidate SHA mismatch')
 p,q=source_polynomials(json.loads(candidate.read_text()))
 require(len(p)==81 and len(q)==81,'expected physical polynomial degree80 /41 Laguerre coefficients')
 require(list(map(str,p))==exact['norm'] and list(map(str,q))==exact['wing'],'exact Laguerre transform coefficient mismatch')
 cmd=[sys.executable,str(here/'generate_kernel_cells.py'),'--candidate',str(candidate),'--partition',str(partition),'--output',str(out/'raw'),'--chunk-size','48']
 with (out/'generation.stdout').open('w') as stdout,(out/'generation.stderr').open('w') as stderr:
  result=subprocess.run(cmd,stdout=stdout,stderr=stderr)
 require(result.returncode==0,'exact-rational generator failed; see logs')
 sources=out/'source';sources.mkdir()
 body='import G40Certificate\nset_option autoImplicit false\nnamespace RH080.Gaussian40\ndef normSource : List ℚ := '+llist(p)+'\ndef wingSource : List ℚ := '+llist(q)+'\nend RH080.Gaussian40\n'
 (sources/'G40Sources.lean').write_text(HEADER+body)
 require((sources/'G40Sources.lean').read_bytes()==(here/'G40Sources.lean').read_bytes(),'regenerated actual input module differs')
 rows=[]
 for row in manifest['chunks']:
  name=row['module'];old=name.replace('G40Cells','GaussianCells')
  text=(out/'raw'/f'{old}.lean').read_text().replace('import GaussianSources\n','import G40Sources\nset_option autoImplicit false\n').replace('RHOnePrime.GaussianKernel','RH080.Gaussian40')
  target=sources/f'{name}.lean';target.write_text(HEADER+text)
  require(sha(target)==row['sha256'],'regenerated cell source SHA mismatch: '+name)
  require(target.read_bytes()==(here/target.name).read_bytes(),'current source differs from manifest: '+name)
  rows.append({'module':name,'bytes':target.stat().st_size,'sha256':sha(target)})
 require(len(rows)==25,'expected25 cell chunks')
 cell_data=json.loads((out/'raw/CELL_DATA.json').read_text());require(cell_data['rows']==1193,'expected1193 cells')
 receipt={'status':'PASS_DETERMINISTIC_REGENERATION_25_CELL_SOURCES_AND_ACTUAL_INPUTS','scope':'exact source byte reproduction, not Lean kernel verification','seconds':time.monotonic()-start,'python':sys.version,'command':cmd,'candidate_sha256':sha(candidate),'partition_sha256':sha(partition),'coefficient_module_sha256':sha(sources/'G40Sources.lean'),'parameters':{'laguerre_degree':40,'physical_degree':80,'cells':1193,'chunk_size':48,'finite_cutoff':12,'taylor_terms':8,'exp_taylor_terms':24,'exp_rounding_bits':256,'cell_rounding_bits':80,'seed':None},'sources':rows,'generator_sha256':sha(here/'generate_kernel_cells.py'),'arithmetic_sha256':sha(here/'prototype_cells.py'),'wrapper_sha256':sha(Path(__file__))}
 temp=out/'REGENERATION_RECEIPT.pending';temp.write_text(json.dumps(receipt,indent=2)+'\n');temp.rename(out/'REGENERATION_RECEIPT.json')
 print(json.dumps({'status':receipt['status'],'seconds':receipt['seconds'],'cells':1193,'sources':len(rows)}))
if __name__=='__main__':main()
