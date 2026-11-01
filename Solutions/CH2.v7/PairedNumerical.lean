/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PairedResult
import NumericEnvelope

open Complex Filter Topology Set MeasureTheory
namespace CH2QRH

/-- A numerical ray bound from the paired power estimate; continuation uses exp(u)>=1+u. -/
theorem paired_power_numerical {x : ℝ} (hx : Real.exp 300 ≤ x) :
    (1 / 384) * Real.log x ^ 2 * x ^ (-(1 : ℝ) / 8) ≤ (1214 : ℝ) / 10 ^ 17 := by
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
  change (1 / 384) * L ^ 2 * Real.exp (-L / 8) ≤ _
  have hh := mul_le_mul_of_nonneg_left hmul (by norm_num : (0 : ℝ) ≤ 1 / 384)
  have hh2 := mul_le_mul_of_nonneg_left hexp (by norm_num : (0 : ℝ) ≤ (1 / 384) * 300 ^ 2)
  norm_num at hh hh2 ⊢
  nlinarith

/-- The original CH2 allowance is more than eighty-six times the new paired numerical bound. -/
theorem old_CH2_allowance_gt_eighty_six {x : ℝ} (hx : 0 < x) :
    86 * ((1214 : ℝ) / 10 ^ 17) <
      Real.pi / (3 * (10 : ℝ) ^ 12) + 113.67 / Real.sqrt x := by
  have hp := Real.pi_gt_d6
  have hn : 0 ≤ (113.67 : ℝ) / Real.sqrt x := by positivity
  norm_num at hn ⊢
  linarith

end CH2QRH
