#!/usr/bin/env python3
"""Generate actual finite Gaussian integral assemblies; no acceptance claim."""
import argparse,json,math
from fractions import Fraction as Q
from pathlib import Path

def lit(x):
 x=Q(x);return f'({x.numerator}/{x.denominator} : ℚ)'
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--cells',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();dat=json.loads((a.cells/'raw/CELL_DATA.json').read_text());a.out.mkdir(exist_ok=True);chunks=[n.replace('GaussianCells','Scaled40Cells')for n in dat['chunks']]
 for name,mode,left,cap in [('norm','true',Q(0),Q('.829128182417')),('wing','false',Q('1772453850905/1000000000000')*Q(4,5),Q('.027759103822'))]:
  rows=[row for row in dat['cells']if row['family']==name];names=[name+str(row['index']).zfill(3)for row in rows];total=sum((Q(row['data']['upper'])for row in rows),Q(0))
  if total>cap:raise ValueError('Finite cap too small')
  lines=['import G40Assembly']+['import '+n for n in chunks]+['set_option autoImplicit false','set_option maxRecDepth 1000000','set_option maxHeartbeats 0','open scoped BigOperators Interval','open MeasureTheory Set Polynomial','namespace RH080Next.Scaled40','open RH080.Gaussian40',f'def {name}Cells : List GaussianCellData := ['+','.join(names)+']',f'theorem {name}_finite_integral : (∫ u in ({lit(left)} : ℝ)..12, positivePartOrAbs {mode} (coeffEval {name}Source u)*Real.exp (-(u^2))) ≤ ({lit(cap)} : ℝ) := by',f'  have hp : cellsConsecutive {lit(left)} 12 {name}Cells = true := by decide +kernel',f'  have hv : ∀ d ∈ {name}Cells, CellValid {mode} {name}Source d := by',f'    simp only [{name}Cells, List.forall_mem_cons, List.forall_mem_nil, and_true]','    exact ⟨'+','.join(n+'_valid'for n in names)+',by simp⟩',f'  have hi := cells_integral_upper {mode} {name}Source {name}Cells {lit(left)} 12 hp hv',f'  have hc : ({name}Cells.map GaussianCellData.upper).sum ≤ {lit(cap)} := by decide +kernel',f'  exact hi.trans (Rat.cast_le.mpr hc)',f'#print axioms {name}_finite_integral','end RH080Next.Scaled40']
  (a.out/('Scaled40Finite'+name.title()+'.lean')).write_text('\n'.join(lines)+'\n')
if __name__=='__main__':main()
