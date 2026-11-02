/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Whole
import PsiToTheta
import IEANTN.Nodes.FKS.v2.Conclusions

namespace FKS2Correction
open Real IEANTN

theorem poly_exp_decreasing (n : ℕ) {c L0 L : ℝ} (hL0 : 0 < L0) (hc : (n : ℝ) / L0 ≤ c)
    (hL : L0 ≤ L) : L ^ n * Real.exp (-c * L) ≤ L0 ^ n * Real.exp (-c * L0) := by
  have hLpos : 0 < L := lt_of_lt_of_le hL0 hL
  have hratio_pos : (0 : ℝ) < L / L0 := div_pos hLpos hL0
  have hlog_ratio : Real.log (L / L0) ≤ L / L0 - 1 := Real.log_le_sub_one_of_pos hratio_pos
  have hlog_sub : Real.log L - Real.log L0 ≤ (L - L0) / L0 := by
    have heq : Real.log (L / L0) = Real.log L - Real.log L0 :=
      Real.log_div (ne_of_gt hLpos) (ne_of_gt hL0)
    have heq2 : L / L0 - 1 = (L - L0) / L0 := by field_simp
    linarith [hlog_ratio, heq, heq2]
  have hkey : (n : ℝ) * (Real.log L - Real.log L0) ≤ c * (L - L0) := by
    have hLsub_nonneg : (0 : ℝ) ≤ L - L0 := by linarith
    have hstep1 : (n : ℝ) * (Real.log L - Real.log L0) ≤ (n : ℝ) * ((L - L0) / L0) :=
      mul_le_mul_of_nonneg_left hlog_sub (Nat.cast_nonneg n)
    have hstep2 : (n : ℝ) * ((L - L0) / L0) ≤ c * (L - L0) := by
      have hmm := mul_le_mul_of_nonneg_right hc hLsub_nonneg
      calc (n : ℝ) * ((L - L0) / L0) = ((n : ℝ) / L0) * (L - L0) := by ring
        _ ≤ c * (L - L0) := hmm
    linarith
  have hrw : ∀ v : ℝ, 0 < v →
      Real.exp ((n : ℝ) * Real.log v - c * v) = v ^ n * Real.exp (-c * v) := by
    intro v hvpos
    have hsplit : (n : ℝ) * Real.log v - c * v = ((n : ℝ) * Real.log v) + (-c * v) := by ring
    rw [hsplit, Real.exp_add]
    congr 1
    rw [show (n : ℝ) * Real.log v = Real.log (v ^ n) from (Real.log_pow v n).symm]
    exact Real.exp_log (by positivity)
  have hexp_le : Real.exp ((n : ℝ) * Real.log L - c * L)
      ≤ Real.exp ((n : ℝ) * Real.log L0 - c * L0) := by
    apply Real.exp_le_exp.mpr; linarith [hkey]
  rw [hrw L hLpos, hrw L0 hL0] at hexp_le
  exact hexp_le

theorem exp_neg_nat_upper (n : ℕ) : exp (-(n : ℝ)) ≤ (10 / 27 : ℝ) ^ n := by
  have h27 : (27 / 10 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have hp : (27 / 10 : ℝ) ^ n ≤ exp (n : ℝ) := by
    rw [← Real.exp_one_pow n]
    exact pow_le_pow_left₀ (by norm_num) h27 n
  rw [exp_neg, ← one_div]
  calc
    1 / exp (n : ℝ) ≤ 1 / (27 / 10 : ℝ) ^ n :=
      one_div_le_one_div_of_le (by positivity) hp
    _ = (10 / 27 : ℝ) ^ n := by rw [← one_div_pow]; norm_num


end FKS2Correction
