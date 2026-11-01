/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PairedError

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- A shared contour remainder with the spectral contribution removed. -/
noncomputable def finiteRemainder (T x : ℝ) : ℝ :=
  let U := T - 1 / 2
  Real.pi / U +
    2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
      1.8 / Real.log x ^ 3) / U ^ 2 +
    (2 * Real.pi / U + 1 / 2) / x * (x ^ (-2 : ℝ) / (1 - x ^ (-2 : ℝ))) +
    Real.pi ^ 2 / (3 * U ^ 2) + Real.log (2 * Real.pi) / x

/-- Explicitly separate the shared remainder from the paired spectral term. -/
theorem pairedError_eq (T β x : ℝ) :
    pairedErrorBound T β x = finiteRemainder T x +
      spectralBound T * ((x ^ β + x ^ (1 - β)) / (2 * x)) := by
  unfold pairedErrorBound finiteErrorBound finiteRemainder
  ring

set_option maxHeartbeats 2000000 in
/-- Uniform remainder estimate at the natural QRH height. -/
theorem scaled_remainder_le {x : ℝ} (hx : Real.exp 128 ≤ x) :
    finiteRemainder (x ^ ((1 : ℝ) / 8)) x * x ^ ((1 : ℝ) / 8) ≤ 3.2 := by
  have hx0 : 0 < x := (Real.exp_pos (128 : ℝ)).trans_le hx
  have hL : 128 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (128 : ℝ)) hx
    simpa using hh
  have hL0 : 0 < Real.log x := by linarith
  set T := x ^ ((1 : ℝ) / 8) with hT
  set U := T - 1 / 2 with hU
  have hTe : T = Real.exp (Real.log x / 8) := by
    rw [hT, Real.rpow_def_of_pos hx0]
    congr 1
    ring
  have hT0 : 0 < T := by rw [hTe]; positivity
  have hTlo : (1000000 : ℝ) ≤ T := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    have h16 : (1000000 : ℝ) ≤ Real.exp 16 := by norm_num at hh; linarith
    exact h16.trans (by rw [hTe]; exact Real.exp_le_exp.mpr (by linarith))
  have hlogT : Real.log T = Real.log x / 8 := by rw [hTe, Real.log_exp]
  have hU0 : 0 < U := by dsimp [U]; linarith
  have hUlo : (0.99 : ℝ) * T ≤ U := by dsimp [U]; linarith
  have hinv : T / U ^ 2 ≤ 2 / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]
    nlinarith [sq_nonneg (U - 0.99 * T)]
  have hinv' : T / U ^ 2 ≤ (2 : ℝ) / 1000000 :=
    hinv.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hTlo)
  have hTx : T ^ 2 ≤ x := by
    rw [hTe, ← Real.exp_nat_mul]
    rw [← Real.exp_log hx0]
    apply Real.exp_le_exp.mpr
    norm_num
    linarith
  have hTdiv : T / x ≤ (1 : ℝ) / 1000000 := by
    have hh : T / x ≤ 1 / T := by rw [div_le_div_iff₀ hx0 hT0]; nlinarith
    exact hh.trans (one_div_le_one_div_of_le (by norm_num) hTlo)
  have hpi : Real.pi / U * T ≤ (3.19 : ℝ) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hU0]
    have hp := Real.pi_lt_d2
    nlinarith
  have hJL : 10 * Real.log T ^ 2 / Real.log x ^ 2 ≤ (1 : ℝ) := by
    rw [hlogT, div_le_iff₀ (by positivity)]
    nlinarith
  have he : Real.exp (-(3 / 2 * (Real.log x - 1))) ≤ 1 / x := by
    calc _ ≤ Real.exp (-Real.log x) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / x := by rw [Real.exp_neg, Real.exp_log hx0, one_div]
  have hJT : Real.exp (-(3 / 2 * (Real.log x - 1))) * (15 + 2 * T) ≤ (1 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right he (show 0 ≤ 15 + 2 * T by positivity)
    have ht : 15 + 2 * T ≤ x := by nlinarith
    have hg : 1 / x * (15 + 2 * T) ≤ (1 : ℝ) := by
      rw [one_div_mul_eq_div, div_le_one hx0]
      exact ht
    exact hh.trans hg
  have hJ : horizontalCorrection T T x ≤ 2 := by unfold horizontalCorrection; linarith
  have hK : Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3 ≤ 1 := by
    have hg := Real.eulerMascheroniConstant_lt_two_thirds
    have h1 : Real.eulerMascheroniConstant / Real.log x ^ 2 ≤ (1 / 2 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h2 : (1.8 : ℝ) / Real.log x ^ 3 ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 128) hL 3
      norm_num at hh
      linarith
    linarith
  have hC : (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
      1.8 / Real.log x ^ 3) / U ^ 2) * T ≤ (0.001 : ℝ) := by
    have hJK : horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3 ≤ 3 := by linarith
    have heq : (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3) / U ^ 2) * T =
        (2 * (horizontalCorrection T T x + Real.eulerMascheroniConstant / Real.log x ^ 2 +
        1.8 / Real.log x ^ 3)) * (T / U ^ 2) := by ring
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right (show 2 * (horizontalCorrection T T x +
      Real.eulerMascheroniConstant / Real.log x ^ 2 + 1.8 / Real.log x ^ 3) ≤ 6 by linarith)
      (show 0 ≤ T / U ^ 2 by positivity)
    have hh2 := mul_le_mul_of_nonneg_left hinv' (by norm_num : (0 : ℝ) ≤ 6)
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

/-- The endpoint inequality and its monotone continuation, checked by real arithmetic. -/
theorem paired_envelope_bound {x : ℝ} (hx : Real.exp 128 ≤ x) :
    pairedErrorBound (x ^ ((1 : ℝ) / 8)) (7 / 8) x ≤
      (1 / 384) * Real.log x ^ 2 * x ^ (-(1 : ℝ) / 8) := by
  have hx0 : 0 < x := (Real.exp_pos (128 : ℝ)).trans_le hx
  have hL : 128 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (128 : ℝ)) hx
    simpa using hh
  have hx1 : 1 ≤ x := by
    have hh := Real.add_one_le_exp (128 : ℝ)
    linarith
  set R := Real.log x / 8 with hR
  set T := x ^ ((1 : ℝ) / 8) with hT
  have hR16 : 16 ≤ R := by dsimp [R]; linarith
  have hR0 : 0 ≤ R := by linarith
  have hTe : T = Real.exp R := by
    rw [hT, Real.rpow_def_of_pos hx0, hR]
    congr 1
    ring
  have hT0 : 0 < T := by rw [hTe]; positivity
  have hTlo : (1000000 : ℝ) ≤ T := by
    have hh := (CH2Section7A.exp_nat_bounds 16).1
    have h16 : (1000000 : ℝ) ≤ Real.exp 16 := by norm_num at hh; linarith
    exact h16.trans (by rw [hTe]; exact Real.exp_le_exp.mpr hR16)
  have hlogT : Real.log T = R := by rw [hTe, Real.log_exp]
  have h1 : x ^ ((7 : ℝ) / 8) * T = x := by
    rw [hT, ← Real.rpow_add hx0]
    norm_num
  have h2 : x ^ (1 - (7 : ℝ) / 8) * T = x * x ^ (-(3 : ℝ) / 4) := by
    calc _ = x ^ ((1 : ℝ) / 4) := by rw [hT, ← Real.rpow_add hx0]; norm_num
      _ = x ^ (1 : ℝ) * x ^ (-(3 : ℝ) / 4) := by rw [← Real.rpow_add hx0]; norm_num
      _ = _ := by rw [Real.rpow_one]
  have hscale : ((x ^ ((7 : ℝ) / 8) + x ^ (1 - (7 : ℝ) / 8)) / (2 * x)) * T =
      (1 + x ^ (-(3 : ℝ) / 4)) / 2 := by
    field_simp
    nlinarith
  have hinv : x ^ (-(1 : ℝ) / 8) = 1 / T := by
    rw [show -(1 : ℝ) / 8 = -(1 / 8 : ℝ) by ring, Real.rpow_neg hx0.le, ← hT, one_div]
  have hq : x ^ (-(3 : ℝ) / 4) ≤ (1 : ℝ) / 1000000 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : -(3 : ℝ) / 4 ≤ -1 / 8)
    rw [hinv] at hh
    exact hh.trans (one_div_le_one_div_of_le (by norm_num) hTlo)
  have hC0 : 0 ≤ spectralBound T := by unfold spectralBound; rw [hlogT]; positivity
  have hCup : spectralBound T ≤ 0.1593 * R ^ 2 + 2.319 * R := by
    unfold spectralBound
    rw [hlogT]
    have hp := Real.pi_pos
    have hp2 := Real.pi_gt_d2
    have hcoef : 1 / (2 * Real.pi) ≤ (0.1593 : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hcoef2 : 2 + 1 / Real.pi ≤ (2.319 : ℝ) := by
      have hh : 1 / Real.pi ≤ (0.319 : ℝ) := by rw [div_le_iff₀ hp]; linarith
      linarith
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg R)
    have hh2 := mul_le_mul_of_nonneg_right hcoef2 hR0
    rw [one_div_mul_eq_div] at hh
    linarith
  have hspec : spectralBound T * ((x ^ ((7 : ℝ) / 8) + x ^ (1 - (7 : ℝ) / 8)) / (2 * x)) * T ≤
      0.0797 * R ^ 2 + 1.16 * R := by
    rw [mul_assoc, hscale]
    have hh := mul_le_mul_of_nonneg_left (show (1 + x ^ (-(3 : ℝ) / 4)) / 2 ≤
      (0.500001 : ℝ) by linarith) hC0
    have hh2 := mul_le_mul_of_nonneg_right hCup (by norm_num : (0 : ℝ) ≤ 0.500001)
    nlinarith [sq_nonneg R]
  have hrem := scaled_remainder_le hx
  have hpoly : (3.2 : ℝ) + 0.0797 * R ^ 2 + 1.16 * R ≤ R ^ 2 / 6 := by
    nlinarith [sq_nonneg (R - 16)]
  have hb : pairedErrorBound T (7 / 8) x * T ≤ Real.log x ^ 2 / 384 := by
    rw [pairedError_eq, add_mul]
    have heq : Real.log x ^ 2 / 384 = R ^ 2 / 6 := by dsimp [R]; ring
    rw [heq]
    linarith
  rw [hinv, mul_one_div]
  apply (le_div_iff₀ hT0).mpr
  calc pairedErrorBound T (7 / 8) x * T ≤ Real.log x ^ 2 / 384 := hb
    _ = (1 / 384) * Real.log x ^ 2 := by ring

end CH2QRH
