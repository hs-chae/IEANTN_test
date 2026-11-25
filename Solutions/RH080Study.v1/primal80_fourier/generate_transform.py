#!/usr/bin/env python3
"""Generate the degree80 Fourier association from the exact new coefficient input.

Generation is untrusted: Lean checks the rational transform against G40Sources.
"""
from fractions import Fraction as Q
import hashlib, json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PRIMAL=HERE.parent/'functional/primal40'
HEADER='''/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
'''
def need(ok,message):
    if not ok:raise RuntimeError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
data=json.loads((PRIMAL/'COEFFICIENTS_EXACT.json').read_text())
need(data['candidate_sha256']=='dbe388a3208a982e9d9f725f2bac16071ac4ddacb45c7d0cac548a6db6884da9','Candidate identity differs')
p=[Q(x) for x in data['norm']];q=[Q(x) for x in data['wing']]
need(len(p)==len(q)==81,'Expected81physicalpositions')
need(all(p[i]==q[i]==0 for i in range(1,81,2)),'Odd physical position is nonzero')
def step(xs):
    out=[Q(0)]*(len(xs)+2)
    for k in range(len(out)):
        if k+2<len(xs):out[k]-=Q((k+2)*(k+1),4)*xs[k+2]
        if k<len(xs):out[k]+=Q(2*k+1,2)*xs[k]
        if k>=2:out[k]-=xs[k-2]
    while out and out[-1]==0:out.pop()
    return out
result=[]
for c in reversed(p[::2]):
    result=step(result)
    if not result:result=[Q(0)]
    result[0]+=c
    while result and result[-1]==0:result.pop()
need(result==q,'Exact independent rationalFouriertransform differs')
literal=lambda x:f'({x.numerator}/{x.denominator} : ℚ)'
source=HEADER+'''import GaussianRationalTransform
import G40Sources

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial
namespace RH080.Primal80Fourier
open RHOnePrime.GaussianFourier
open RHOnePrime.GaussianKernel

/- The exact41even coefficients of the actual degree80 physical source.
All81positions, including zero odd positions, are checked against G40Sources. -/
'''
source+='def normEvenSource : List ℚ := ['+','.join(map(literal,p[::2]))+']\n'
source+='def wingEvenSource : List ℚ := ['+','.join(map(literal,q[::2]))+']\n'
source+='''
lemma actual_norm_expansion : evenSource normEvenSource = RH080.Gaussian40.normSource++[0] := by
  decide +kernel

lemma actual_wing_expansion : evenSource wingEvenSource = RH080.Gaussian40.wingSource++[0] := by
  decide +kernel

/-- Actual rational transform, including all81outputpositions. No native axiom. -/
theorem actual_even_transform : evenTransform normEvenSource =
    coeffPoly RH080.Gaussian40.wingSource := by
  have checked : evenTransformCoeffs normEvenSource = RH080.Gaussian40.wingSource := by
    decide +kernel
  rw [←coeffPoly_evenTransformCoeffs, checked]

theorem actual_source_transform :
    transformSource RH080.Gaussian40.normSource =
      (coeffPoly RH080.Gaussian40.wingSource).map (Rat.castHom ℂ) := by
  have checked := transform_evenSource normEvenSource
  rw [actual_norm_expansion, transformSource_append_zero, actual_even_transform] at checked
  exact checked

#print axioms actual_norm_expansion
#print axioms actual_wing_expansion
#print axioms actual_even_transform
#print axioms actual_source_transform
end RH080.Primal80Fourier
'''
(HERE/'Primal80CoefficientTransform.lean').write_text(source)
record=dict(candidate_sha256=data['candidate_sha256'],laguerre_degree=40,physical_degree=80,physical_position_count=81,even_position_count=41,norm=[str(x) for x in p],wing=[str(x) for x in q],exact_independent_transform_agrees=True,source_inputs=[dict(path=str(f.relative_to(HERE.parents[2])),sha256=sha(f)) for f in [PRIMAL/'COEFFICIENTS_EXACT.json',PRIMAL/'G40Sources.lean']],generated_sha256=sha(HERE/'Primal80CoefficientTransform.lean'),status='FROZEN_EXACT_INPUTS_AND_GENERATED_KERNEL_CHECK_PENDING')
(HERE/'INPUTS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['candidate_sha256','physical_position_count','exact_independent_transform_agrees','generated_sha256']}))
