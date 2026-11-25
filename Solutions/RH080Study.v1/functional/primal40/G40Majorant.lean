/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40CoeffArithmetic
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
set_option autoImplicit false
namespace RH080.Gaussian40

def positivePartOrAbs (absMode : Bool) (x : ℝ) : ℝ := if absMode then |x| else max 0 x

def coeffMajorant (absMode : Bool) (cs : List ℚ) : List ℚ :=
  if 0 ≤ coeffLower cs then cs
  else if coeffUpper cs ≤ 0 then
    if absMode then coeffScale (-1) cs else []
  else [max (-(coeffLower cs)) (coeffUpper cs)]

theorem continuous_positivePartOrAbs (absMode : Bool) (cs : List ℚ) :
    Continuous (fun t => positivePartOrAbs absMode (coeffEval cs t)) := by
  cases absMode
  · exact continuous_const.max (continuous_coeffEval cs)
  · exact (continuous_coeffEval cs).abs

/-- A genuine pointwise abs/positive-part majorant, including all uncertain-root cells. -/
theorem coeffMajorant_sound (absMode : Bool) (cs : List ℚ) (t : ℝ)
    (ht : t ∈ Icc 0 1) :
    positivePartOrAbs absMode (coeffEval cs t) ≤
      coeffEval (coeffMajorant absMode cs) t := by
  have hl := coeffEval_lower cs t ht
  have hu := coeffEval_upper cs t ht
  unfold coeffMajorant
  split_ifs with hpos hneg hmode
  · have hpos' : (0 : ℝ) ≤ (coeffLower cs : ℝ) := by exact_mod_cast hpos
    have hp : 0 ≤ coeffEval cs t := hpos'.trans hl
    cases absMode <;> simp [positivePartOrAbs, abs_of_nonneg hp, max_eq_right hp]
  · simp only [coeffEval_scale, Rat.cast_neg, Rat.cast_one, neg_mul, one_mul]
    have hn : coeffEval cs t ≤ 0 := hu.trans (by exact_mod_cast hneg)
    cases absMode <;> simp_all [positivePartOrAbs, abs_of_nonpos hn]
  · have hn : coeffEval cs t ≤ 0 := hu.trans (by exact_mod_cast hneg)
    cases absMode <;> simp_all [positivePartOrAbs, coeffEval, max_eq_left hn]
  · simp only [coeffEval, mul_zero, add_zero, Rat.cast_max, Rat.cast_neg]
    have hm1 : -(coeffLower cs : ℝ) ≤ max (-(coeffLower cs : ℝ)) (coeffUpper cs : ℝ) := le_max_left _ _
    have hm2 : (coeffUpper cs : ℝ) ≤ max (-(coeffLower cs : ℝ)) (coeffUpper cs : ℝ) := le_max_right _ _
    have hz : 0 ≤ max (-(coeffLower cs : ℝ)) (coeffUpper cs : ℝ) := by
      have : (coeffLower cs : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hpos
      linarith
    cases absMode
    · exact max_le hz (hu.trans hm2)
    · exact abs_le.mpr ⟨by linarith, hu.trans hm2⟩

#print axioms coeffMajorant_sound
end RH080.Gaussian40
