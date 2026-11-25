#!/usr/bin/env python3
"""Regenerate all exact degree56 input coefficients and 1135 kernel-checkable cells.

No numerical generation result is a Lean acceptance receipt. This program checks
byte equality with the frozen, independently compiled source manifest. Standard
library only; no randomness. Use a fresh experiment-owned --out directory.
"""
from pathlib import Path
from fractions import Fraction
import argparse,hashlib,json,subprocess,sys,time
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/"primal40"))
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
 candidate=here/'CANDIDATE_LAGUERRE28.json';partition=here/'PARTITION.json'
 exact=json.loads((here/'COEFFICIENTS_EXACT.json').read_text());manifest=json.loads((here/'CELL_SOURCE_MANIFEST.json').read_text())
 require(sha(candidate)==exact['candidate_sha256'],'candidate SHA mismatch')
 p,q=source_polynomials(json.loads(candidate.read_text()))
 original=json.loads((here/'OPT28_ORIGINAL.json').read_text())
 require(list(map(Fraction,original['polynomial_in_y_squared']))==p[::2] and not any(p[1::2]),'original timely input differs from actual physical polynomial')
 require(sha(here/'OPT28_ORIGINAL.json')==exact['original_source_sha256'],'original timely input SHA mismatch')
 require(len(p)==57 and len(q)==57,'expected physical polynomial degree56 /41 Laguerre coefficients')
 require(list(map(str,p))==exact['norm'] and list(map(str,q))==exact['wing'],'exact Laguerre transform coefficient mismatch')
 cmd=[sys.executable,str(here.parent/'primal40/generate_kernel_cells.py'),'--candidate',str(candidate),'--partition',str(partition),'--output',str(out/'raw'),'--chunk-size','48']
 with (out/'generation.stdout').open('w') as stdout,(out/'generation.stderr').open('w') as stderr:
  result=subprocess.run(cmd,stdout=stdout,stderr=stderr)
 require(result.returncode==0,'exact-rational generator failed; see logs')
 sources=out/'source';sources.mkdir()
 body='import G40Certificate\nset_option autoImplicit false\nnamespace RH080.Gaussian28\nopen RH080.Gaussian40\ndef normSource : List ℚ := '+llist(p)+'\ndef wingSource : List ℚ := '+llist(q)+'\nend RH080.Gaussian28\n'
 (sources/'G28Sources.lean').write_text(HEADER+body)
 require((sources/'G28Sources.lean').read_bytes()==(here/'G28Sources.lean').read_bytes(),'regenerated actual input module differs')
 rows=[]
 for row in manifest['chunks']:
  name=row['module'];old=name.replace('G28Cells','GaussianCells')
  text=(out/'raw'/f'{old}.lean').read_text().replace('import GaussianSources\n','import G28Sources\nset_option autoImplicit false\n').replace('namespace RHOnePrime.GaussianKernel','namespace RH080.Gaussian28\nopen RH080.Gaussian40').replace('end RHOnePrime.GaussianKernel','end RH080.Gaussian28')
  target=sources/f'{name}.lean';target.write_text(HEADER+text)
  require(sha(target)==row['sha256'],'regenerated cell source SHA mismatch: '+name)
  require(target.read_bytes()==(here/target.name).read_bytes(),'current source differs from manifest: '+name)
  rows.append({'module':name,'bytes':target.stat().st_size,'sha256':sha(target)})
 require(len(rows)==24,'expected24 cell chunks')
 cell_data=json.loads((out/'raw/CELL_DATA.json').read_text());require(cell_data['rows']==1135,'expected1135 cells')
 receipt={'status':'PASS_DETERMINISTIC_REGENERATION_24_CELL_SOURCES_AND_ACTUAL_INPUTS','scope':'exact source byte reproduction, not Lean kernel verification','seconds':time.monotonic()-start,'python':sys.version,'command':cmd,'candidate_sha256':sha(candidate),'partition_sha256':sha(partition),'coefficient_module_sha256':sha(sources/'G28Sources.lean'),'parameters':{'laguerre_degree':28,'physical_degree':56,'cells':1135,'chunk_size':48,'finite_cutoff':12,'taylor_terms':8,'exp_taylor_terms':24,'exp_rounding_bits':256,'cell_rounding_bits':80,'seed':None},'sources':rows,'generator_sha256':sha(here.parent/'primal40/generate_kernel_cells.py'),'arithmetic_sha256':sha(here.parent/'primal40/prototype_cells.py'),'wrapper_sha256':sha(Path(__file__))}
 temp=out/'REGENERATION_RECEIPT.pending';temp.write_text(json.dumps(receipt,indent=2)+'\n');temp.rename(out/'REGENERATION_RECEIPT.json')
 print(json.dumps({'status':receipt['status'],'seconds':receipt['seconds'],'cells':1135,'sources':len(rows)}))
if __name__=='__main__':main()
