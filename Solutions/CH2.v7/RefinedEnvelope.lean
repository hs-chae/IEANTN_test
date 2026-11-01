/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PairedNumerical

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH
open CH2.v7

/-- The endpoint inequality and its monotone continuation, checked by real arithmetic. -/
theorem paired_refined_envelope_bound {x : ℝ} (hx : Real.exp 300 ≤ x) :
    pairedErrorBound (x ^ ((1 : ℝ) / 8)) (7 / 8) x ≤
      (1 / 566) * Real.log x ^ 2 * x ^ (-(1 : ℝ) / 8) := by
  have hx0 : 0 < x := (Real.exp_pos (300 : ℝ)).trans_le hx
  have hL : 300 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (300 : ℝ)) hx
    simpa using hh
  have hx1 : 1 ≤ x := by
    have hh := Real.add_one_le_exp (300 : ℝ)
    linarith
  set R := Real.log x / 8 with hR
  set T := x ^ ((1 : ℝ) / 8) with hT
  have hR16 : 16 ≤ R := by dsimp [R]; linarith
  have hR375 : 37.5 ≤ R := by dsimp [R]; linarith
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
  have hrem := scaled_remainder_le ((Real.exp_le_exp.mpr (by norm_num : (128 : ℝ) ≤ 300)).trans hx)
  have hpoly : (3.2 : ℝ) + 0.0797 * R ^ 2 + 1.16 * R ≤ 64 * R ^ 2 / 566 := by
    nlinarith [sq_nonneg (R - 37.5)]
  have hb : pairedErrorBound T (7 / 8) x * T ≤ Real.log x ^ 2 / 566 := by
    rw [pairedError_eq, add_mul]
    have heq : Real.log x ^ 2 / 566 = 64 * R ^ 2 / 566 := by dsimp [R]; ring
    rw [heq]
    linarith
  rw [hinv, mul_one_div]
  apply (le_div_iff₀ hT0).mpr
  calc pairedErrorBound T (7 / 8) x * T ≤ Real.log x ^ 2 / 566 := hb
    _ = (1 / 566) * Real.log x ^ 2 := by ring

/-- A numerical ray bound from the paired power estimate; continuation uses exp(u)>=1+u. -/
theorem refined_power_numerical {x : ℝ} (hx : Real.exp 300 ≤ x) :
    (1 / 566) * Real.log x ^ 2 * x ^ (-(1 : ℝ) / 8) ≤ (824 : ℝ) / 10 ^ 17 := by
  have hx0 : 0 < x := (Real.exp_pos (300 : ℝ)).trans_le hx
  have hL : 300 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos (300 : ℝ)) hx
    simpa using hh
  set L := Real.log x with hLdef
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have he := Real.add_one_le_exp ((L - 300) / 16)
  have hbound : L ≤ 300 * Real.exp ((L - 300) / 16) := by dsimp [L] at he ⊢; linarith
  have hsq := pow_le_pow_left₀ hL0 hbound 2
  have heq : Real.exp ((L - 300) / 16) ^ 2 * Real.exp (-L / 8) = Real.exp (-(37.5 : ℝ)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right hsq (Real.exp_pos (-L / 8)).le
  have hr : x ^ (-(1 : ℝ) / 8) = Real.exp (-L / 8) := by
    rw [Real.rpow_def_of_pos hx0]
    congr 1
    dsimp [L]
    ring
  rw [mul_pow, mul_assoc, heq] at hmul
  obtain ⟨_, _, _, h37⟩ := exp_bounds_36_300
  have hexp : Real.exp (-(37.5 : ℝ)) ≤ 1 / 19320000000000000 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) h37
  rw [hr]
  change (1 / 566) * L ^ 2 * Real.exp (-L / 8) ≤ _
  have hh := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 1 / 566)
  have hh2 := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ (1 / 566) * 300 ^ 2)
  norm_num at hh hh2 ⊢
  nlinarith

/-- The original CH2 allowance is more than one hundred twenty-seven times the new paired numerical bound. -/
theorem old_CH2_allowance_gt_one_hundred_twenty_seven {x : ℝ} (hx : 0 < x) :
    127 * ((824 : ℝ) / 10 ^ 17) <
      Real.pi / (3 * (10 : ℝ) ^ 12) + 113.67 / Real.sqrt x := by
  have hp := Real.pi_gt_d6
  have hn : 0 ≤ (113.67 : ℝ) / Real.sqrt x := by positivity
  norm_num at hn ⊢
  linarith


end CH2QRH
