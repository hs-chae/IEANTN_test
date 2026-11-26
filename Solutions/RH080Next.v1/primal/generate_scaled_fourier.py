#!/usr/bin/env python3
"""Generate the new candidate's actual Fourier association; Lean checks it."""
import argparse,hashlib,json,re,sys
from fractions import Fraction as Q
from pathlib import Path

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();old=Path(__file__).resolve().parents[2]/'RH080Study.v1';sys.path.insert(0,str(old/'functional/primal40'));from generate_kernel_cells import source_polynomials,llist
 dat=json.loads(a.candidate.read_text());p,q=source_polynomials(dat)
 if len(p)!=81 or Q(str(dat['scale']))!=Q(5,4):raise ValueError('Expected frozen degree80scale5/4 candidate')
 a.out.mkdir(exist_ok=True)
 text=(old/'primal80_fourier/Primal80CoefficientTransform.lean').read_text().replace('import G40Sources','import Scaled40Sources').replace('RH080.Primal80Fourier','RH080Next.Scaled40Fourier')
 for name,cs in [('normEvenSource',p[::2]),('wingEvenSource',q[::2])]:text=re.sub(r'def '+name+r' : List ℚ := \[[^\n]*\]', 'def '+name+' : List ℚ := '+llist(cs),text)
 for name in ['normSource','wingSource']:text=text.replace('RH080.Gaussian40.'+name,'RH080Next.Scaled40.'+name)
 (a.out/'Scaled40CoefficientTransform.lean').write_text(text)
 functions='''import Scaled40Sources
noncomputable section
namespace RH080Next.Scaled40
open RH080.Gaussian40
def baseF (x : ℝ) : ℝ := coeffEval normSource (Real.sqrt Real.pi*x)*Real.exp (-((Real.sqrt Real.pi*x)^2))
def baseG (x : ℝ) : ℝ := coeffEval wingSource (Real.sqrt Real.pi*x)*Real.exp (-((Real.sqrt Real.pi*x)^2))
def physicalF (x : ℝ) : ℝ := baseF ((5/4)*x)
def physicalG (x : ℝ) : ℝ := (4/5)*baseG ((4/5)*x)
end RH080Next.Scaled40
''';(a.out/'Scaled40Functions.lean').write_text(functions)
 text=(old/'primal80_fourier/Primal80ActualFourier.lean').read_text().replace('import Primal80CoefficientTransform','import Scaled40CoefficientTransform\nimport GaussianDilation').replace('import G40Functions','import Scaled40Functions').replace('RH080.Primal80Fourier','RH080Next.Scaled40Fourier')
 for name in ['normSource','wingSource']:text=text.replace('RH080.Gaussian40.'+name,'RH080Next.Scaled40.'+name)
 text=text.replace('RH080.Gaussian40.physicalF','RH080Next.Scaled40.baseF').replace('RH080.Gaussian40.physicalG','RH080Next.Scaled40.baseG')
 text=text.replace('end RH080Next.Scaled40Fourier','''
/-- Actual Fourier transform of the new scaled degree80 candidate. -/
theorem fourier_scaled_physical (t : ℝ) :
    𝓕 (fun x : ℝ => (RH080Next.Scaled40.physicalF x : ℂ)) t =
      (RH080Next.Scaled40.physicalG t : ℂ) := by
  have hf := RH080Next.Primal.fourier_pair_dilate
    RH080Next.Scaled40.baseF RH080Next.Scaled40.baseG
    (fun t => congrFun fourier_actual_physical t) (s := (5/4 : ℝ)) (by norm_num) t
  convert hf using 1 <;> simp only [RH080Next.Scaled40.physicalF, RH080Next.Scaled40.physicalG]
  congr 2 <;> ring
#print axioms fourier_scaled_physical
end RH080Next.Scaled40Fourier''')
 (a.out/'Scaled40ActualFourier.lean').write_text(text)
 result={'status':'GENERATED_KERNEL_PENDING','candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in a.out.glob('Scaled40*Fourier.lean')}};(a.out/'FOURIER_INPUTS.json').write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
