/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LeanCert.Core.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! Kernel arithmetic for the actual sine integral in the CMS cosine kernel.
The identification with the Fourier kernel's L1 norm remains a separate analytic
source proposition. This file supplies numerical bounds on genuine integrals,
not an assumed hardcoded certificate. -/
namespace RHOnePrimeEvolution.CMSNumerics
open Real intervalIntegral
set_option autoImplicit false
set_option maxHeartbeats 0

noncomputable def sincPoly (x : ℝ) : ℝ :=
  1 - x^2/6 + x^4/120 - x^6/5040 + x^8/362880 - x^10/39916800 + x^12/6227020800

noncomputable def sincUpper (x : ℝ) : ℝ := sincPoly x + x^13/87178291200

lemma sin_taylor14 (x : ℝ) :
    (∑ i ∈ Finset.range 14, (iteratedDeriv i sin 0 / i.factorial) * x^i) =
      x * sincPoly x := by
  norm_num [Finset.sum_range_succ, iteratedDeriv_succ', Real.deriv_sin,
    Real.deriv_cos', iteratedDeriv_fun_neg, sincPoly]
  <;> ring

lemma sinc_le_upper {x : ℝ} (hx : 0 ≤ x) : sinc x ≤ sincUpper x := by
  by_cases hz : x = 0
  · subst x; norm_num [sincUpper, sincPoly]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hz)
  have hb := LeanCert.Core.taylor_remainder_bound (a := (0 : ℝ)) (b := x) (c := 0)
    (n := 14) (M := 1) hx le_rfl hx Real.contDiff_sin
    (fun y _ => by simpa [Real.norm_eq_abs] using Real.abs_iteratedDeriv_sin_le_one 14 y)
    (by norm_num) x ⟨hx, le_rfl⟩
  rw [sin_taylor14] at hb
  simp only [sub_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg hx] at hb
  have hh := (abs_le.mp hb).2
  rw [Real.sinc_of_ne_zero hz]
  apply (div_le_iff₀ hxpos).mpr
  norm_num [sincUpper] at hh ⊢
  nlinarith

lemma integral_upper_exact :
    (∫ x in (0 : ℝ)..π, sincUpper x) =
      π - π^3/18 + π^5/600 - π^7/35280 + π^9/3265920 -
        π^11/439084800 + π^13/80951270400 + π^14/1220496076800 := by
  simp only [sincUpper, sincPoly]
  simp (disch := (first | (apply Continuous.intervalIntegrable; fun_prop) | positivity))
    [integral_add, integral_sub, integral_div, integral_pow]
  <;> ring

theorem sine_integral_upper : (∫ x in (0 : ℝ)..π, sinc x) ≤ 463/250 := by
  have hm : (∫ x in (0 : ℝ)..π, sinc x) ≤ ∫ x in (0 : ℝ)..π, sincUpper x := by
    apply intervalIntegral.integral_mono_on Real.pi_pos.le
      (Real.continuous_sinc.intervalIntegrable 0 π)
      ((by unfold sincUpper sincPoly; fun_prop : Continuous sincUpper).intervalIntegrable 0 π)
    intro x hx; exact sinc_le_upper hx.1
  rw [integral_upper_exact] at hm
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.141592) Real.pi_gt_d6.le 3
  have h7 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.141592) Real.pi_gt_d6.le 7
  have h11 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3.141592) Real.pi_gt_d6.le 11
  have h5 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 5
  have h9 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 9
  have h13 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 13
  have h14 := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 14
  norm_num at h3 h7 h11 h5 h9 h13 h14
  linarith [Real.pi_lt_d6]

theorem cosine_kernel_numerator_lower :
    (19013/20000 : ℝ) ≤ 4 * sin (9*π/20) - 3 := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := π/20)
  have hs : sin (9*π/20) = cos (π/20) := by
    rw [← Real.cos_pi_div_two_sub]; congr 1; ring
  rw [hs]
  have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d6.le 2
  norm_num at hp
  nlinarith

theorem cosine_kernel_ratio_lower (hpos : 0 < ∫ x in (0 : ℝ)..π, sinc x) :
    (2281/2000 : ℝ) ≤
      (4 * sin (9*π/20) - 3) / ((9/20) * ∫ x in (0 : ℝ)..π, sinc x) := by
  apply (le_div_iff₀ (by positivity : 0 < (9/20 : ℝ) * ∫ x in (0 : ℝ)..π, sinc x)).mpr
  linarith [sine_integral_upper, cosine_kernel_numerator_lower]

theorem sine_integral_pos : 0 < ∫ x in (0 : ℝ)..π, sinc x := by
  apply intervalIntegral.integral_pos Real.pi_pos Real.continuous_sinc.continuousOn
  · intro x hx
    rw [Real.sinc_of_ne_zero (ne_of_gt hx.1)]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2) hx.1.le
  · exact ⟨0, ⟨le_rfl, Real.pi_pos.le⟩, by simp⟩

noncomputable def cmsJ : ℝ :=
  (4 * sin (9*π/20) - 3) / ((9/20) * ∫ x in (0 : ℝ)..π, sinc x)

theorem actual_cmsJ_lower : (2281/2000 : ℝ) ≤ cmsJ :=
  cosine_kernel_ratio_lower sine_integral_pos

#print axioms sine_integral_upper
#print axioms cosine_kernel_numerator_lower
#print axioms cosine_kernel_ratio_lower
#print axioms sine_integral_pos
#print axioms actual_cmsJ_lower
end RHOnePrimeEvolution.CMSNumerics
