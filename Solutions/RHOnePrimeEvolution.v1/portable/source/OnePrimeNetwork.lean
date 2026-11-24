/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHOnePrimeEvolution.v1.Conclusions
import CMSSharperUniform
import CMSContinuousFrontier
import CMSFiniteBenchmarks
import FiniteGapRefined

/-! Canonical interfaces consume the actual numerical node as a proof parameter.
There is no auxiliary source conjunction or unused numerical premise. -/
namespace RHOnePrimeEvolution.v1
open Real Set
open RHOnePrime.CMSGeometry RHOnePrime.CMSPrime RHOnePrime.CMSOpen
set_option autoImplicit false
set_option maxHeartbeats 0

theorem challenge_kernel_ratio_lower : kernel_ratio_lower :=
  RHOnePrime.CMSSharper.actual_cmsJ_sharper

lemma closed_from_numeric (hCMS : CMSCosineInput.v1.obstruction) (rh : RH.v1.hypothesis)
    (hJ : kernel_ratio_lower) {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeClosed x (x + (8767 / 10000) * sqrt x * log x) := by
  change SourceCMS616 at hCMS
  change (28517 / 25000 : ℝ) ≤ RHOnePrimeEvolution.CMSNumerics.cmsJ at hJ
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hx
  suffices HasPrimeClosed (exp (log x))
      (exp (log x) + (8767 / 10000) * sqrt (exp (log x)) * log x) by
    simpa only [Real.exp_log hx0] using this
  by_contra hp
  have hob := hCMS rh (log x) (8767 / 10000) hL ⟨by norm_num, by norm_num⟩ hp
  have hm0 := mainScale_nonneg (by norm_num : (4 / 5 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hL
  have hm := mainScale_lower (by norm_num : (4 / 5 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hL
  have hz := logScale_upper (by norm_num : (4 / 5 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hL
  have hroom := RHOnePrime.CMSSharper.logarithmic_room hL
  have hmul := mul_le_mul_of_nonneg_right hJ hm0
  have hlow := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 28517 / 25000)
  norm_num at *
  nlinarith

theorem challenge_late_open_08768 (hCMS : CMSCosineInput.v1.obstruction) (rh : RH.v1.hypothesis)
    (hJ : kernel_ratio_lower) : late_open_08768 := by
  intro x hx
  have h := open_of_shifted_closed (by norm_num : (0 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hx (closed_from_numeric hCMS rh hJ (by linarith : exp 44 ≤ x + 1))
  norm_num at h ⊢
  exact h

theorem challenge_uniform_open_08768 (hlate : late_open_08768)
    (hgap : PrimeGapTable.v1.gaps) : uniform_open_08768 := by
  intro x hx
  by_cases h : x < exp 44
  · exact RHOnePrime.FiniteGap.finite_coefficient_0004 hgap (by norm_num) hx h
  · exact hlate x (le_of_not_gt h)

theorem challenge_finite_slab_open_08301 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) : finite_slab_open_08301 := by
  intro x hlo hhi
  exact open_prime_08301 hCMS rh hlo hhi

theorem challenge_finite_absolute_1551 (hgap : PrimeGapTable.v1.gaps) : finite_absolute_1551 := by
  intro x hx hhi
  exact RHOnePrime.FiniteGap.finite_constant_window hgap hx hhi

theorem challenge_consecutive_gap_08768 (hi : uniform_open_08768) :
    consecutive_gap_08768 := by
  intro p q hp hq hpq hpLarge hconsec
  obtain ⟨r, hr, hpr, hrupper⟩ := hi p hpLarge
  have hpr' : p < r := by exact_mod_cast hpr
  have hqr : q ≤ r := by
    by_contra h
    exact hconsec r hpr' (Nat.lt_of_not_ge h) hr
  have hqr' : (q : ℝ) ≤ r := by exact_mod_cast hqr
  linarith

theorem challenge_continuous_late (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) : continuous_late := by
  intro x hx
  exact RHOnePrime.CMSContinuous.open_prime_continuous hCMS rh hx

theorem challenge_continuous_improves_uniform : continuous_improves_uniform := by
  intro x hx
  exact RHOnePrime.CMSContinuous.continuous_endpoint_lt_uniform hx

theorem challenge_continuous_uniform (hlate : continuous_late)
    (hgap : PrimeGapTable.v1.gaps) : continuous_uniform := by
  intro x hx
  split_ifs with h
  · exact RHOnePrime.FiniteGap.finite_constant_window hgap hx h
  · exact hlate x (le_of_not_gt h)

theorem challenge_bounded_open_08357 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) (hgap : PrimeGapTable.v1.gaps) : bounded_open_08357 := by
  intro x hx hhi
  by_cases h : x < exp 44
  · exact RHOnePrime.FiniteGap.finite_coefficient_0004 hgap (by norm_num) hx h
  · exact RHOnePrime.CMSFinite.open_prime_08357 hCMS rh (le_of_not_gt h) hhi

theorem challenge_bounded_open_08512 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) (hgap : PrimeGapTable.v1.gaps) : bounded_open_08512 := by
  intro x hx hhi
  by_cases h : x < exp 44
  · exact RHOnePrime.FiniteGap.finite_coefficient_0004 hgap (by norm_num) hx h
  · exact RHOnePrime.CMSFinite.open_prime_08512 hCMS rh (le_of_not_gt h) hhi

theorem challenge_bounded_open_08185 (hCMS : CMSCosineInput.v1.obstruction)
    (rh : RH.v1.hypothesis) (hgap : PrimeGapTable.v1.gaps) : bounded_open_08185 := by
  intro x hx hhi
  by_cases h : x < exp 44
  · exact RHOnePrime.FiniteGap.finite_coefficient_0004 hgap (by norm_num) hx h
  · exact RHOnePrime.CMSTight.open_prime_08185 hCMS rh (le_of_not_gt h) hhi

#print axioms challenge_kernel_ratio_lower
#print axioms challenge_late_open_08768
#print axioms challenge_uniform_open_08768
#print axioms challenge_finite_slab_open_08301
#print axioms challenge_finite_absolute_1551
#print axioms challenge_consecutive_gap_08768
#print axioms challenge_continuous_late
#print axioms challenge_continuous_improves_uniform
#print axioms challenge_continuous_uniform
#print axioms challenge_bounded_open_08357
#print axioms challenge_bounded_open_08512
#print axioms challenge_bounded_open_08185
end RHOnePrimeEvolution.v1
