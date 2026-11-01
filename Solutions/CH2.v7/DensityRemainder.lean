/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityOuter
import GeneralStrip

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

set_option maxHeartbeats 2000000 in
/-- A uniform remainder estimate for the actual larger density truncation heights. -/
theorem density_scaled_remainder {T x : ℝ} (hTlo : 1000000 ≤ T) (hxlo : 1000000 ≤ x)
    (hL : 64 ≤ Real.log x) (hlogT : Real.log T ≤ (3 / 4) * Real.log x)
    (hTdiv : T / x ≤ (1 : ℝ) / 1000000) :
    finiteRemainder T x * T ≤ 3.2 := by
  have hT0 : 0 < T := by linarith
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  set U := T - 1 / 2 with hU
  have hU0 : 0 < U := by dsimp [U]; linarith
  have hUlo : (0.99 : ℝ) * T ≤ U := by dsimp [U]; linarith
  have hinv : T / U ^ 2 ≤ 2 / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]
    nlinarith [sq_nonneg (U - 0.99 * T)]
  have hinv' : T / U ^ 2 ≤ (2 : ℝ) / 1000000 :=
    hinv.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hTlo)
  have hpi : Real.pi / U * T ≤ (3.19 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hU0]
    have hp := Real.pi_lt_d2
    nlinarith
  have hJL : 10 * Real.log T ^ 2 / Real.log x ^ 2 ≤ (6 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hh := pow_le_pow_left₀ hlogT0 hlogT 2
    nlinarith
  have he : Real.exp (-(3 / 2 * (Real.log x - 1))) ≤ 1 / x := by
    calc _ ≤ Real.exp (-Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / x := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
  have hJT : Real.exp (-(3 / 2 * (Real.log x - 1))) * (15 + 2 * T) ≤ (1 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right he (show 0 ≤ 15 + 2 * T by positivity)
    have ht : 15 + 2 * T ≤ x := by
      have hh := (div_le_iff₀ hx0).mp hTdiv
      norm_num at hh
      nlinarith
    have hg : 1 / x * (15 + 2 * T) ≤ (1 : ℝ) := by
      rw [one_div_mul_eq_div, div_le_one hx0]
      exact ht
    exact hh.trans hg
  have hJ : horizontalCorrection T T x ≤ 7 := by unfold horizontalCorrection; linarith
  have hK : Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 ≤ 1 := by
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have h1 : Real.eulerMascheroniConstant / Real.log x ^ 2 ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : (1.8 : ℝ) / Real.log x ^ 3 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 64) hL 3
      norm_num at hh
      linarith
    linarith
  have hC : (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
      1.8 / Real.log x ^ 3) / U ^ 2) * T ≤ (0.001 : ℝ) := by
    have hJK : horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3 ≤ 8 := by linarith
    have heq : (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / U ^ 2) * T =
        (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3)) * (T / U ^ 2) := by ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right (show 2 * (horizontalCorrection T T x +
      Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3) ≤ 16 by linarith)
      (show 0 ≤ T / U ^ 2 by positivity)
    have hh2 := mul_le_mul_of_nonneg_left hinv' (by norm_num : (0 : ℝ) ≤ 16)
    norm_num at hh2 ⊢
    linarith
  have hPole : Real.pi ^ 2 / (3 * U ^ 2) * T ≤ (0.001 : ℝ) := by
    have heq : Real.pi ^ 2 / (3 * U ^ 2) * T = (Real.pi ^ 2 / 3) * (T / U ^ 2) := by ring
    rw [heq]
    have hp2 : Real.pi ^ 2 / 3 ≤ (16 / 3 : ℝ) := by
      have hp := Real.pi_pos
      have hp4 := Real.pi_lt_four
      nlinarith
    have hh := mul_le_mul hp2 hinv' (by positivity) (by norm_num : (0 : ℝ) ≤ 16 / 3)
    norm_num at hh ⊢
    linarith
  have hLog : Real.log (2 * Real.pi) / x * T ≤ (0.001 : ℝ) := by
    have hl : Real.log (2 * Real.pi) ≤ (8 : ℝ) := by
      have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
      linarith [Real.pi_lt_four]
    rw [show Real.log (2 * Real.pi) / x * T = Real.log (2 * Real.pi) * (T / x) by ring]
    have hh := mul_le_mul hl hTdiv (by positivity) (by norm_num : (0 : ℝ) ≤ 8)
    norm_num at hh ⊢
    linarith
  have hTail : ((2 * Real.pi / U + 1 / 2) / x *
      (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) * T ≤ (0.001 : ℝ) := by
    have hx2 : 2 ≤ x := by nlinarith
    have hp := Real.pi_pos
    have hxp : x ^ (-2 : ℝ) ≤ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg hx0.le, Real.rpow_two, inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith
    have hden : 0 < 1 - x ^ (-2 : ℝ) := by linarith
    have hz0 : 0 ≤ x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)) := by positivity
    have hz1 : x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)) ≤ (1 : ℝ) := by
      rw [div_le_one hden]
      linarith
    have hc : 2 * Real.pi / U + 1 / 2 ≤ (1 : ℝ) := by
      have hh : 2 * Real.pi / U ≤ (1 / 2 : ℝ) := by
        rw [div_le_iff₀ hU0]
        have hp4 := Real.pi_lt_four
        nlinarith
      linarith
    have heq : ((2 * Real.pi / U + 1 / 2) / x *
        (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ)))) * T =
        (2 * Real.pi / U + 1 / 2) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) * (T / x) := by ring
    rw [heq]
    have hh : (2 * Real.pi / U + 1 / 2) * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) ≤ 1 := by
      exact (mul_le_mul hc hz1 hz0 (by norm_num)).trans_eq (by ring)
    have hh2 := mul_le_mul_of_nonneg_right hh (show 0 ≤ T / x by positivity)
    norm_num at hh2 hTdiv ⊢
    linarith
  unfold finiteRemainder
  change (Real.pi / U + _ + _ + _ + _) * T ≤ _
  rw [add_mul, add_mul, add_mul, add_mul]
  linarith

end CH2QRH
