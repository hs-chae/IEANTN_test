/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Elementary, source-independent transfer of a genuine psi error envelope
to its absolutely convergent weighted tail. No prime-sum normalization or
literature premise is assumed here. -/

namespace LambdaEvolutionA
open Real Set MeasureTheory Filter

noncomputable def psiRemainder (t : ℝ) : ℝ := Chebyshev.psi t - t
noncomputable def psiTailIntegrand (t : ℝ) : ℝ := (Chebyshev.psi t - t) / t ^ 2

theorem measurable_psiTailIntegrand : Measurable psiTailIntegrand := by
  exact (Chebyshev.psi_mono.measurable.sub measurable_id).div (measurable_id.pow_const 2)

theorem integrableOn_compact_remainder {X : ℝ} :
    IntegrableOn psiTailIntegrand (Icc 1 X) := by
  change IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) / t ^ 2) (Icc 1 X)
  have hp : IntegrableOn (fun t : ℝ ↦ Chebyshev.psi t - t) (Icc 1 X) :=
    (Chebyshev.psi_mono.monotoneOn _).integrableOn_isCompact isCompact_Icc |>.sub
      (continuous_id.continuousOn.integrableOn_Icc)
  have hc : ContinuousOn (fun t : ℝ ↦ (t ^ 2)⁻¹) (Icc 1 X) := by
    apply (continuous_id.pow 2).continuousOn.inv₀
    intro t ht
    change t ^ 2 ≠ 0
    exact pow_ne_zero 2 (lt_of_lt_of_le zero_lt_one ht.1).ne'
  simpa only [div_eq_mul_inv] using
    hp.mul_continuousOn hc isCompact_Icc

theorem integrableOn_one_of_tail {X : ℝ} (hX : 1 ≤ X)
    (hI : IntegrableOn psiTailIntegrand (Ioi X)) :
    IntegrableOn psiTailIntegrand (Ioi 1) := by
  rw [← Ioc_union_Ioi_eq_Ioi hX]
  exact (integrableOn_compact_remainder.mono_set Ioc_subset_Icc_self).union hI

theorem tail_integrand_le_power {X C t : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ y ≥ X, IEANTN.Eψ y ≤ C * y ^ (-(1 : ℝ) / 8)) (ht : X ≤ t) :
    |psiTailIntegrand t| ≤ C * t ^ (-(9 : ℝ) / 8) := by
  have hp : 0 < t := lt_of_lt_of_le zero_lt_one (hX.trans ht)
  calc
    |psiTailIntegrand t| = IEANTN.Eψ t / t := by
      simp only [psiTailIntegrand, IEANTN.Eψ, abs_div, abs_of_nonneg (sq_nonneg t)]
      field_simp
    _ ≤ (C * t ^ (-(1 : ℝ) / 8)) / t :=
      div_le_div_of_nonneg_right (hbound t ht) hp.le
    _ = C * t ^ (-(9 : ℝ) / 8) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one t, mul_assoc, ← Real.rpow_add hp]
      norm_num

theorem integrableOn_tail_of_power_bound {X C : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ C * t ^ (-(1 : ℝ) / 8)) :
    IntegrableOn psiTailIntegrand (Ioi X) := by
  apply ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-(9 : ℝ) / 8) < -1)
    (lt_of_lt_of_le zero_lt_one hX)).const_mul C).mono'
      measurable_psiTailIntegrand.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simpa only [Real.norm_eq_abs] using tail_integrand_le_power hX hbound ht.le

theorem integrableOn_one_of_power_bound {X C : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ C * t ^ (-(1 : ℝ) / 8)) :
    IntegrableOn psiTailIntegrand (Ioi 1) :=
  integrableOn_one_of_tail hX (integrableOn_tail_of_power_bound hX hbound)

theorem abs_tail_integral_le_power {X C x : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ C * t ^ (-(1 : ℝ) / 8)) (hx : X ≤ x) :
    |∫ t in Ioi x, psiTailIntegrand t| ≤ 8 * C * x ^ (-(1 : ℝ) / 8) := by
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one (hX.trans hx)
  have hI := (integrableOn_tail_of_power_bound hX hbound).mono_set (Ioi_subset_Ioi hx)
  have hM := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(9 : ℝ) / 8) < -1)
    hp).const_mul C
  calc
    |∫ t in Ioi x, psiTailIntegrand t| ≤ ∫ t in Ioi x, |psiTailIntegrand t| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Ioi x, C * t ^ (-(9 : ℝ) / 8) := by
      apply integral_mono_ae hI.abs hM
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact tail_integrand_le_power hX hbound (hx.trans ht.le)
    _ = 8 * C * x ^ (-(1 : ℝ) / 8) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hp]
      norm_num
      ring

theorem abs_remainder_minus_tail_le_power {X C x : ℝ} (hX : 1 ≤ X)
    (hbound : ∀ t ≥ X, IEANTN.Eψ t ≤ C * t ^ (-(1 : ℝ) / 8)) (hx : X ≤ x) :
    |(Chebyshev.psi x - x) / x - ∫ t in Ioi x, psiTailIntegrand t| ≤
      9 * C * x ^ (-(1 : ℝ) / 8) := by
  have hp : 0 < x := lt_of_lt_of_le zero_lt_one (hX.trans hx)
  have hpoint : |(Chebyshev.psi x - x) / x| ≤ C * x ^ (-(1 : ℝ) / 8) := by
    simpa only [abs_div, abs_of_pos hp, IEANTN.Eψ] using hbound x hx
  have htail := abs_tail_integral_le_power hX hbound hx
  calc
    _ ≤ |(Chebyshev.psi x - x) / x| + |∫ t in Ioi x, psiTailIntegrand t| :=
      abs_sub _ _
    _ ≤ C * x ^ (-(1 : ℝ) / 8) + 8 * C * x ^ (-(1 : ℝ) / 8) := add_le_add hpoint htail
    _ = _ := by ring

#print axioms integrableOn_one_of_power_bound
#print axioms abs_tail_integral_le_power
#print axioms abs_remainder_minus_tail_le_power
end LambdaEvolutionA
