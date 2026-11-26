/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapData
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RH080Next.FapPV.Model
open Data

/-- Pure finite mathematical specification. Input-only literals are traversed
linearly; this does not assume the C implementation or any output. -/
def enc (j : Nat) : Nat := Data.encodedNode j
def pos (e : Nat) : Nat := e-Data.scale
def neg (e : Nat) : Nat := Data.scale-e
def magnitude (a b : Nat) : Nat := if b≤a then a-b else b-a
def rightNodes : List Nat := Data.encoded.drop 1 ++ [Data.scale]
def right2Nodes : List Nat := Data.encoded.drop 2 ++ [Data.scale,Data.scale]

def firstPositive : Nat :=
  pos (enc 0) + 2*((Data.encoded.drop 1).map pos).sum

def firstNegative : Nat :=
  neg (enc 0) + 2*((Data.encoded.drop 1).map neg).sum

def f0Numerator : Nat := firstPositive-firstNegative

/-- Twice the positive affine-cell area, rounded upward in coefficient units. -/
def positiveCell (left right : Nat) : Nat :=
  if Data.scale≤left then
    if Data.scale≤right then pos left+pos right
    else (pos left*pos left+(pos left+neg right)-1)/(pos left+neg right)
  else
    if Data.scale<right then
      (pos right*pos right+(pos right+neg left)-1)/(pos right+neg left)
    else 0

def positiveAreaNumerator : Nat :=
  (List.zipWith positiveCell (Data.encoded.drop 80) (rightNodes.drop 80)).sum

def heightNumerator : Nat :=
  pos (enc 80) +
    (List.zipWith (fun a b => pos b-pos a)
      (Data.encoded.drop 80) (rightNodes.drop 80)).sum

def firstVariationNumerator : Nat :=
  2*(List.zipWith magnitude Data.encoded rightNodes).sum

def derivativeVariationNumerator : Nat :=
  (2*80)*(magnitude (enc 1) (enc 0) +
    (List.zipWith (fun a bc => magnitude (a+bc.2) (2*bc.1))
      Data.encoded (rightNodes.zip right2Nodes)).sum)

def absRoundedValue (e : Nat) : Nat :=
  (magnitude e Data.scale+9999999)/10000000

/-- Upward rounding of an absolute nodal value to a multiple of 10⁻⁹. -/
def absNodeRounded (j : Nat) : Nat := absRoundedValue (enc j)

def secondMomentNumerator : Nat :=
  ((Data.encoded.zip rightNodes).zipIdx.map fun p =>
    absRoundedValue p.1.1*(6*p.2*p.2+4*p.2+1) +
      absRoundedValue p.1.2*(6*p.2*p.2+8*p.2+3)).sum

def maximumNumerator : Nat :=
  (Data.encoded.map fun e => magnitude e Data.scale).foldl max 0

/-- The generic, already-published normalized meanings of the seven outputs. -/
def f0Value : ℚ := (f0Numerator : ℚ)/(80*10000000000000000)
def positiveAreaUpper : ℚ := (positiveAreaNumerator : ℚ)/(80*10000000000000000)
def heightValue : ℚ := (heightNumerator : ℚ)/10000000000000000
def firstVariationValue : ℚ := (firstVariationNumerator : ℚ)/10000000000000000
def derivativeVariationValue : ℚ := (derivativeVariationNumerator : ℚ)/10000000000000000
def secondMomentUpper : ℚ := (secondMomentNumerator : ℚ)/(6*80^3*1000000000)
def maximumValue : ℚ := (maximumNumerator : ℚ)/10000000000000000

/-- Mathematical specification evaluation only. The corresponding actual
source-AST execution is proved separately; this theorem alone is not PV. -/
theorem f0Numerator_exact : f0Numerator=799999999999990000 := by decide +kernel
theorem positiveAreaNumerator_exact : positiveAreaNumerator=16297236881532502 := by
  decide +kernel
theorem heightNumerator_exact : heightNumerator=1142770022680000 := by decide +kernel
theorem firstVariationNumerator_exact : firstVariationNumerator=14047086942420000 := by
  decide +kernel
theorem derivativeVariationNumerator_exact : derivativeVariationNumerator=40617111385600000 := by
  decide +kernel
theorem secondMomentNumerator_exact : secondMomentNumerator=760944122290429 := by
  decide +kernel
theorem maximumNumerator_exact : maximumNumerator=6915614327570000 := by decide +kernel

theorem positivePart_difference (e : Nat) :
    (pos e : Int)-(neg e : Int)=(e : Int)-(Data.scale : Int) := by
  unfold pos neg
  by_cases h : Data.scale≤e
  · rw [Nat.sub_eq_zero_of_le h, Int.natCast_sub h]
    simp
  · have he : e≤Data.scale := by omega
    rw [Nat.sub_eq_zero_of_le he, Int.natCast_sub he]
    omega

theorem roundedAbsNode_upper (j : Nat) :
    magnitude (enc j) Data.scale ≤ absNodeRounded j*10000000 := by
  unfold absNodeRounded absRoundedValue
  omega

#print axioms f0Numerator_exact
#print axioms positiveAreaNumerator_exact
#print axioms heightNumerator_exact
#print axioms firstVariationNumerator_exact
#print axioms derivativeVariationNumerator_exact
#print axioms secondMomentNumerator_exact
#print axioms maximumNumerator_exact
#print axioms positivePart_difference
#print axioms roundedAbsNode_upper

end RH080Next.FapPV.Model
