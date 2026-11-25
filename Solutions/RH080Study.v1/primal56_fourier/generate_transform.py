#!/usr/bin/env python3
"""Generate the degree56 Fourier association from the exact new coefficient input.

Generation is untrusted: Lean checks the rational transform against G28Sources.
"""
from fractions import Fraction as Q
import hashlib, json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PRIMAL=HERE.parent/'functional/primal28'
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
need(data['candidate_sha256']=='057330776a0aedb31bbf455fdbf611012e41ebd3eb35b77b47d07fb7e9fb2656','Candidate identity differs')
p=[Q(x) for x in data['norm']];q=[Q(x) for x in data['wing']]
need(len(p)==len(q)==57,'Expected57physicalpositions')
need(all(p[i]==q[i]==0 for i in range(1,57,2)),'Odd physical position is nonzero')
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
import G28Sources

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Polynomial
namespace RH080.Primal56Fourier
open RHOnePrime.GaussianFourier
open RHOnePrime.GaussianKernel

/- The exact29even coefficients of the actual degree56 physical source.
All57positions, including zero odd positions, are checked against G28Sources. -/
'''
source+='def normEvenSource : List ℚ := ['+','.join(map(literal,p[::2]))+']\n'
source+='def wingEvenSource : List ℚ := ['+','.join(map(literal,q[::2]))+']\n'
source+='''
lemma actual_norm_expansion : evenSource normEvenSource = RH080.Gaussian28.normSource++[0] := by
  decide +kernel

lemma actual_wing_expansion : evenSource wingEvenSource = RH080.Gaussian28.wingSource++[0] := by
  decide +kernel

/-- Actual rational transform, including all57outputpositions. No native axiom. -/
theorem actual_even_transform : evenTransform normEvenSource =
    coeffPoly RH080.Gaussian28.wingSource := by
  have checked : evenTransformCoeffs normEvenSource = RH080.Gaussian28.wingSource := by
    decide +kernel
  rw [←coeffPoly_evenTransformCoeffs, checked]

theorem actual_source_transform :
    transformSource RH080.Gaussian28.normSource =
      (coeffPoly RH080.Gaussian28.wingSource).map (Rat.castHom ℂ) := by
  have checked := transform_evenSource normEvenSource
  rw [actual_norm_expansion, transformSource_append_zero, actual_even_transform] at checked
  exact checked

#print axioms actual_norm_expansion
#print axioms actual_wing_expansion
#print axioms actual_even_transform
#print axioms actual_source_transform
end RH080.Primal56Fourier
'''
(HERE/'Primal56CoefficientTransform.lean').write_text(source)
record=dict(candidate_sha256=data['candidate_sha256'],laguerre_degree=28,physical_degree=56,physical_position_count=57,even_position_count=29,norm=[str(x) for x in p],wing=[str(x) for x in q],exact_independent_transform_agrees=True,source_inputs=[dict(path=str(f.relative_to(HERE.parents[2])),sha256=sha(f)) for f in [PRIMAL/'COEFFICIENTS_EXACT.json',PRIMAL/'G28Sources.lean']],generated_sha256=sha(HERE/'Primal56CoefficientTransform.lean'),status='FROZEN_EXACT_INPUTS_AND_GENERATED_KERNEL_CHECK_PENDING')
original_file=PRIMAL/'OPT28_ORIGINAL.json'
laguerre_file=PRIMAL/'CANDIDATE_LAGUERRE28.json'
need(sha(original_file)=='1a396b22abfb3827d3d8018787c37608379252b049ddcde8bd924a3b6d8b3b1a','Timely original source identity differs')
original=[Q(x) for x in json.loads(original_file.read_text())['polynomial_in_y_squared']]
weights=[Q(x) for x in json.loads(laguerre_file.read_text())['coefficients_decimal_exact_rationals']]
need(original==p[::2] and len(weights)==29,'Original monomial/physical source differs')
def add(a,b):return [(a[k] if k<len(a) else Q(0))+(b[k] if k<len(b) else Q(0)) for k in range(max(len(a),len(b)))]
def scale(c,a):return [c*x for x in a]
def mul(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
basis=[[Q(1)],[Q(1,2),Q(-2)]]
for n in range(27):
    basis.append(scale(Q(1,n+2),add(mul([Q(2*(n+1))+Q(1,2),Q(-2)],basis[-1]),scale(-(Q(n+1)-Q(1,2)),basis[-2]))))
combined=[]
for c,b in zip(weights,basis):combined=add(combined,scale(c,b))
need(combined==original,'Exact original-to-Laguerre basis association differs')
association=HEADER+'''import Primal56CoefficientTransform
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH080.Primal56Fourier
open RHOnePrime.GaussianFourier RHOnePrime.GaussianKernel

/-- The exact rational recurrence used by the supplied Laguerre-basis file,
in the variable t=y²: L0=1,L1=1/2-2t, and
(n+2)L(n+2)=(2(n+1)+1/2-2t)L(n+1)-(n+1/2)Ln. -/
def basisPair : Nat → List ℚ × List ℚ
  | 0 => ([1],[1/2,-2])
  | n+1 =>
    let previous := basisPair n
    let next := coeffScale (1/((n+2 : Nat) : ℚ))
      (coeffAdd (coeffMul [2*((n+1 : Nat) : ℚ)+1/2,-2] previous.2)
        (coeffScale (-(((n+1 : Nat) : ℚ)-1/2)) previous.1))
    (previous.2,next)

def basisCombination (cs : List ℚ) : List ℚ :=
  ((List.range cs.length).map (fun n =>
    coeffScale ((cs[n]?).getD 0) (basisPair n).1)).foldl coeffAdd []
'''
association+='def originalEvenSource : List ℚ := ['+','.join(map(literal,original))+']\n'
association+='def originalLaguerreWeights : List ℚ := ['+','.join(map(literal,weights))+']\n'
association+='''
/-- Exact finite association of the preserved timely original monomial input
with its rational Laguerre representation. No search/score result is assumed. -/
theorem original_to_laguerre :
    basisCombination originalLaguerreWeights = originalEvenSource := by decide +kernel
theorem original_even_identity : originalEvenSource = normEvenSource := by decide +kernel
theorem original_physical57_identity :
    evenSource originalEvenSource = RH080.Gaussian28.normSource++[0] := by
  rw [original_even_identity]
  exact actual_norm_expansion

/-- The true Fourier adapter consumes the explicit preserved-source/basis
association, not only a posthoc candidate name or numerical output. -/
theorem timely_actual_source_transform :
    transformSource RH080.Gaussian28.normSource =
      (coeffPoly RH080.Gaussian28.wingSource).map (Rat.castHom ℂ) := by
  have h := transform_evenSource (basisCombination originalLaguerreWeights)
  rw [original_to_laguerre,original_even_identity,actual_norm_expansion,
    transformSource_append_zero,actual_even_transform] at h
  exact h
#print axioms original_to_laguerre
#print axioms original_physical57_identity
#print axioms timely_actual_source_transform
end RH080.Primal56Fourier
'''
(HERE/'Primal56OriginalInput.lean').write_text(association)
record['original_source_sha256']=sha(original_file)
record['original_input_module_sha256']=sha(HERE/'Primal56OriginalInput.lean')
record['exact_original_to_laguerre_to_physical57_identity']=True
record['source_inputs'] += [dict(path=str(f.relative_to(HERE.parents[2])),sha256=sha(f)) for f in [original_file,laguerre_file]]
(HERE/'INPUTS.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['candidate_sha256','physical_position_count','exact_independent_transform_agrees','generated_sha256']}))
