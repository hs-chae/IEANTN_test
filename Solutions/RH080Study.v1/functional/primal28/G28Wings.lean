/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G28Physical
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
set_option autoImplicit false
namespace RH080.Gaussian28
open RH080.Gaussian40

theorem physicalG_even (x : ℝ) : physicalG (-x) = physicalG x := by
  simp only [physicalG, mul_neg, wingSource_even, neg_sq]

theorem physicalG_abs (x : ℝ) : physicalG |x| = physicalG x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), physicalG_even]

/-- The actual exterior-of-unit-interval wing equals twice the positive half-wing. -/
theorem physical_wings_identity :
    (∫ x in {x : ℝ | 1 < |x|}, max 0 (physicalG x)) =
      2*(∫ x in Ioi (1 : ℝ), max 0 (physicalG x)) := by
  have hs : MeasurableSet {x : ℝ | 1 < |x|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  rw [← integral_indicator hs]
  have hpoint (x : ℝ) :
      ({x : ℝ | 1 < |x|}).indicator (fun x => max 0 (physicalG x)) x =
      (Ioi (1 : ℝ)).indicator (fun x => max 0 (physicalG x)) |x| := by
    simp only [Set.indicator_apply, mem_ofPred_eq, mem_Ioi, physicalG_abs]
  simp_rw [hpoint]
  rw [integral_comp_abs, setIntegral_indicator measurableSet_Ioi]
  have heq : Ioi (0 : ℝ) ∩ Ioi 1 = Ioi 1 := by
    apply inter_eq_right.mpr
    intro x hx
    change (1 : ℝ) < x at hx
    change (0 : ℝ) < x
    linarith
  rw [heq]

theorem physical_full_wings_upper :
    (∫ x in {x : ℝ | 1 < |x|}, max 0 (physicalG x)) ≤ (313377324/10000000000 : ℝ) := by
  rw [physical_wings_identity]
  exact physical_positive_wing_upper

/-- The precise physical numerical functional; Fourier(F)=G is proved separately. -/
noncomputable def physicalFullInverseObjective : ℝ :=
  (∫ x : ℝ, |physicalF x|)/
    (physicalF 0-(36/11 : ℝ)*(∫ x in {x : ℝ | 1 < |x|}, max 0 (physicalG x)))

theorem physical_full_objective_upper : physicalFullInverseObjective ≤ (833945448/1000000000 : ℝ) := by
  unfold physicalFullInverseObjective
  rw [physical_wings_identity]
  exact gaussian_objective_upper

theorem physical_full_objective_lt_printed_2026 :
    physicalFullInverseObjective < (834050619151/1000000000000 : ℝ) :=
  physical_full_objective_upper.trans_lt (by norm_num)

#print axioms physical_wings_identity
#print axioms physical_full_wings_upper
#print axioms physical_full_objective_lt_printed_2026
end RH080.Gaussian28
