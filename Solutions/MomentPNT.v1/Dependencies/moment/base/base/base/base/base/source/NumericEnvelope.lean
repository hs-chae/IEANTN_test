/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PsiError

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- Rational exponential bounds, using the already proved CH2 exponential estimates. -/
theorem exp_bounds_36_300 :
    (4311100000000000 : ℝ) ≤ Real.exp 36 ∧ Real.exp 36 ≤ 10000000000000000 ∧
    (10 : ℝ) ^ 100 ≤ Real.exp 300 ∧ (19320000000000000 : ℝ) ≤ Real.exp 37.5 := by
  have h36 := CH2Section7A.exp_nat_bounds 36
  have h3 := (CH2Section7A.exp_nat_bounds 3).1
  have h3lo : (10 : ℝ) ≤ Real.exp 3 := by norm_num at h3; linarith
  have h300 : (10 : ℝ) ^ 100 ≤ Real.exp 300 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10) h3lo 100
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh ⊢
    exact hh
  have h37 := (CH2Section7A.exp_nat_bounds 37).1
  norm_num at h36 h37
  have hquarter : (1.2840169 : ℝ) ≤ Real.exp 0.25 := by
    have hh := CH2Section7A.exp_small_ge (by norm_num : (0 : ℝ) ≤ 0.25)
    norm_num at hh ⊢
    linarith
  have hhalf : (1.64869 : ℝ) ≤ Real.exp 0.5 := by
    rw [show (0.5 : ℝ) = 0.25 + 0.25 by norm_num, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp 0.25 - 1.2840169)]
  have hp : Real.exp 37.5 = Real.exp 37 * Real.exp 0.5 := by
    rw [← Real.exp_add]
    norm_num
  rw [hp]
  have hh := mul_le_mul_of_nonneg_left hhalf (Real.exp_pos (37 : ℝ)).le
  constructor
  · linarith [h36.1]
  constructor
  · linarith [h36.2]
  constructor
  · linarith
  · nlinarith

/-- A fully Lean-checked uniform numerical consequence of the free-height transfer.
This uses no floating-point interval result or unproved density-transfer assumption. -/
theorem finiteErrorBound_le_1573e_neg17 {x : ℝ} (hx : Real.exp 300 ≤ x) :
    finiteErrorBound (Real.exp 36) (7 / 8) x ≤ (1573 : ℝ) / 10 ^ 17 := by
  obtain ⟨hTlo, hThi, hXlo, h37⟩ := exp_bounds_36_300
  have hxlo : (10 : ℝ) ^ 100 ≤ x := hXlo.trans hx
  have hx0 : 0 < x := by linarith [show (0 : ℝ) < 10 ^ 100 by norm_num]
  have hxlog : 300 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos (300 : ℝ)) hx
    simpa using h
  have hlog0 : 0 < Real.log x := by linarith
  set T := Real.exp (36 : ℝ) with hT
  set U := T - 1 / 2 with hU
  have hUlo : (4311000000000000 : ℝ) ≤ U := by dsimp [U, T]; linarith
  have hU0 : 0 < U := by linarith
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  have hp6lo := Real.pi_gt_d6
  have hp6hi := Real.pi_lt_d6
  have hlogT : Real.log T = 36 := by simp [T]
  have hspec : spectralBound T ≤ 289.7241 := by
    unfold spectralBound
    rw [hlogT]
    have h1 : (36 : ℝ) ^ 2 / (2 * Real.pi) ≤ 36 ^ 2 / (2 * 3.141592) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    have h2 : 1 / Real.pi ≤ (1 / 3.141592 : ℝ) := one_div_le_one_div_of_le (by norm_num) hp6lo.le
    nlinarith
  have hpower : x ^ ((7 : ℝ) / 8) / x ≤ 1 / 19320000000000000 := by
    rw [← Real.rpow_sub_one hx0.ne', Real.rpow_def_of_pos hx0]
    have he : Real.exp (Real.log x * (7 / 8 - 1)) ≤ Real.exp (-(37.5 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    exact he.trans (by rw [Real.exp_neg, ← one_div]; exact
      one_div_le_one_div_of_le (by norm_num) h37)
  have hspec' : spectralBound T * (x ^ ((7 : ℝ) / 8) / x)
      ≤ 289.7241 / 19320000000000000 := by
    exact (mul_le_mul_of_nonneg_right hspec (by positivity)).trans
      (by simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 289.7241))
  have hpi : Real.pi / U ≤ 3.141593 / 4311000000000000 := by
    exact div_le_div₀ (by norm_num) hp6hi.le (by norm_num) hUlo
  have hJL : 10 * Real.log T ^ 2 / Real.log x ^ 2 ≤ (1 : ℝ) := by
    rw [hlogT, div_le_iff₀ (by positivity)]
    nlinarith
  have htailExp : Real.exp (-(3 / 2 * (Real.log x - 1))) ≤ 1 / (10 : ℝ) ^ 100 := by
    calc _ ≤ Real.exp (-(300 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by rw [Real.exp_neg, ← one_div]; exact
        one_div_le_one_div_of_le (by norm_num) hXlo
  have hJT : Real.exp (-(3 / 2 * (Real.log x - 1))) * (15 + 2 * T) ≤ (1 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right htailExp (show 0 ≤ 15 + 2 * T by positivity)
    have htbound : 15 + 2 * T ≤ (30000000000000000 : ℝ) := by dsimp [T]; linarith
    have hh2 := mul_le_mul_of_nonneg_left htbound (show 0 ≤ 1 / (10 : ℝ) ^ 100 by positivity)
    norm_num at hh hh2 ⊢
    linarith
  have hJ : horizontalCorrection T T x ≤ 2 := by
    unfold horizontalCorrection
    linarith
  have hJ0 : 0 ≤ horizontalCorrection T T x := by unfold horizontalCorrection; positivity
  have hK : Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 ≤ 1 := by
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have h1 : Real.eulerMascheroniConstant / Real.log x ^ 2 ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : (1.8 : ℝ) / Real.log x ^ 3 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 300) hxlog 3
      norm_num at hh
      linarith
    linarith
  have hJK0 : 0 ≤ horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
      1.8 / Real.log x ^ 3 := by
    have hg : 0 < Real.eulerMascheroniConstant := by linarith [Real.one_half_lt_eulerMascheroniConstant]
    positivity
  have hcontour : 2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
      1.8 / Real.log x ^ 3) / U ^ 2 ≤ (1 : ℝ) / 10 ^ 20 := by
    rw [div_le_iff₀ (by positivity)]
    have hU2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4311000000000000) hUlo 2
    norm_num at hU2
    nlinarith
  have hxp : x ^ (-2 : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg hx0.le, Real.rpow_two, inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg (x - 2)]
  have hden : 0 < 1 - x ^ (-2 : ℝ) := by linarith
  have hz : 0 ≤ x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)) := by positivity
  have hz1 : x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)) ≤ (1 : ℝ) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - x ^ (-2 : ℝ))]
    linarith
  have hsmall : (2 * Real.pi / U + 1 / 2) / x ≤ (1 : ℝ) / 10 ^ 20 := by
    have hh : 2 * Real.pi / U + 1 / 2 ≤ (1 : ℝ) := by
      rw [show 2 * Real.pi / U = 2 * (Real.pi / U) by ring]
      linarith
    have hdiv := div_le_div_of_nonneg_right hh hx0.le
    have hx20 : (10 : ℝ) ^ 20 ≤ x := by norm_num at hxlo ⊢; linarith
    exact hdiv.trans (one_div_le_one_div_of_le (by norm_num) hx20)
  have htriv : (2 * Real.pi / U + 1 / 2) / x * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))
      ≤ (1 : ℝ) / 10 ^ 20 := by
    have hh := mul_le_mul_of_nonneg_left hz1 (show 0 ≤ (2 * Real.pi / U + 1 / 2) / x by positivity)
    linarith
  have hpole : Real.pi ^ 2 / (3 * U ^ 2) ≤ (1 : ℝ) / 10 ^ 20 := by
    rw [div_le_iff₀ (by positivity)]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4311000000000000) hUlo 2
    nlinarith [sq_nonneg (Real.pi - 4)]
  have hlog : Real.log (2 * Real.pi) / x ≤ (1 : ℝ) / 10 ^ 20 := by
    have hh : Real.log (2 * Real.pi) ≤ 8 := by
      linarith [Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)]
    rw [div_le_iff₀ hx0]
    have hxx : (8 : ℝ) * 10 ^ 20 ≤ x := by norm_num at hxlo ⊢; linarith
    linarith
  unfold finiteErrorBound
  change Real.pi / U + spectralBound T * (x ^ ((7 : ℝ) / 8) / x) + _ + _ + _ + _ ≤ _
  norm_num at hspec' hpi hcontour htriv hpole hlog ⊢
  linarith

/-- The elementary Mathlib psi-to-theta correction is negligible on this ray. -/
theorem psi_theta_correction_le {x : ℝ} (hx : Real.exp 300 ≤ x) :
    (Chebyshev.psi x - Chebyshev.theta x) / x ≤ (1 : ℝ) / 10 ^ 17 := by
  obtain ⟨_, _, hXlo, h37⟩ := exp_bounds_36_300
  have hx0 : 0 < x := (Real.exp_pos (300 : ℝ)).trans_le hx
  have hx1 : 1 ≤ x := by
    have hh := hXlo.trans hx
    norm_num at hh ⊢
    linarith
  have hl : 300 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (300 : ℝ)) hx
    simpa using hh
  have hlog := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 4)
  have hpoint := Chebyshev.psi_sub_theta_le hx1
  have he : Real.sqrt x * x ^ ((1 : ℝ) / 4) = x * x ^ (-(1 : ℝ) / 4) := by
    calc Real.sqrt x * x ^ ((1 : ℝ) / 4) = x ^ ((1 : ℝ) / 2 + 1 / 4) := by
          rw [Real.sqrt_eq_rpow, Real.rpow_add hx0]
      _ = x ^ (1 : ℝ) * x ^ (-(1 : ℝ) / 4) := by
          rw [← Real.rpow_add hx0]
          norm_num
      _ = x * x ^ (-(1 : ℝ) / 4) := by rw [Real.rpow_one]
  have hcorr : (Chebyshev.psi x - Chebyshev.theta x) / x ≤ 8 * x ^ (-(1 : ℝ) / 4) := by
    calc _ ≤ (2 * Real.sqrt x * Real.log x) / x :=
          div_le_div_of_nonneg_right hpoint hx0.le
      _ ≤ (2 * Real.sqrt x * (x ^ ((1 : ℝ) / 4) / (1 / 4))) / x := by gcongr
      _ = 8 * x ^ (-(1 : ℝ) / 4) := by
        rw [show 2 * Real.sqrt x * (x ^ ((1 : ℝ) / 4) / (1 / 4)) =
          8 * (Real.sqrt x * x ^ ((1 : ℝ) / 4)) by ring, he]
        field_simp
  have h75 : (10 : ℝ) ^ 32 ≤ Real.exp 75 := by
    rw [show (75 : ℝ) = 37.5 + 37.5 by norm_num, Real.exp_add]
    nlinarith [sq_nonneg (Real.exp 37.5 - 19320000000000000)]
  have hpow : x ^ (-(1 : ℝ) / 4) ≤ 1 / (10 : ℝ) ^ 32 := by
    rw [Real.rpow_def_of_pos hx0]
    calc _ ≤ Real.exp (-(75 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := by rw [Real.exp_neg, ← one_div]; exact
        one_div_le_one_div_of_le (by norm_num) h75
  have hh := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 8)
  norm_num at hh ⊢
  linarith

/-- The old CH2 displayed allowance is strictly more than sixty_six times this verified new one. -/
theorem old_CH2_allowance_gt_sixty_six_new {x : ℝ} (hx : 0 < x) :
    66 * ((1573 : ℝ) / 10 ^ 17) <
      Real.pi / (3 * (10 : ℝ) ^ 12) + 113.67 / Real.sqrt x := by
  have hh := Real.pi_gt_d6
  have hn : 0 ≤ (113.67 : ℝ) / Real.sqrt x := by positivity
  norm_num at hn ⊢
  linarith

end CH2QRH
