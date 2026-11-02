/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.BKLNW.v4.Conclusions
import Frontier
import TableReplay
import IEANTN.Nodes.PlattTrudgian2021.v1.Tables
namespace QRHPhase2
open Real IEANTN

open BKLNW.v4

theorem table_power (hpsi : QRHCH2.v2.psi_density_frontier) (b : ℕ) (hb : 200 ≤ b) :
    HasPowerLogBound Eψ (tableCoefficient b) 0 (7 / 8) (exp b) := by
  unfold tableCoefficient
  split_ifs with h1000 h512 h300 h256 h224
  all_goals
    intro x hx
  · have hbR : (1000 : ℝ) ≤ b := by exact_mod_cast h1000
    convert hpsi 1000 0.01014 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr hbR).trans hx) using 1 <;> norm_num
  · have hbR : (512 : ℝ) ≤ b := by exact_mod_cast h512
    convert hpsi 512 0.01117 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr hbR).trans hx) using 1 <;> norm_num
  · have hbR : (300 : ℝ) ≤ b := by exact_mod_cast h300
    convert hpsi 300 0.01310 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr hbR).trans hx) using 1 <;> norm_num
  · have hbR : (256 : ℝ) ≤ b := by exact_mod_cast h256
    convert hpsi 256 0.01411 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr hbR).trans hx) using 1 <;> norm_num
  · have hbR : (224 : ℝ) ≤ b := by exact_mod_cast h224
    convert hpsi 224 0.01526 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr hbR).trans hx) using 1 <;> norm_num
  · have hbR : (192 : ℝ) ≤ b := by exact_mod_cast (show 192 ≤ b by omega)
    convert hpsi 192 0.01713 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr hbR).trans hx) using 1 <;> norm_num

theorem coefficient_le (b : ℕ) : 0 ≤ tableCoefficient b ∧ tableCoefficient b ≤ 0.01713 := by
  unfold tableCoefficient
  split_ifs <;> norm_num

theorem coefficient_strict (b : ℕ) (hb : 224 ≤ b) : tableCoefficient b < 0.01713 := by
  unfold tableCoefficient
  split_ifs <;> norm_num <;> omega

theorem table8_phase2 (hpsi : QRHCH2.v2.psi_density_frontier) :
    ∀ p ∈ BKLNW.v1.table8, 200 ≤ p.1 →
      HasNumericalBound Eψ (tableCoefficient p.1 * exp (-(p.1 : ℝ) / 8)) (exp p.1) ∧
      tableCoefficient p.1 * exp (-(p.1 : ℝ) / 8) < p.2 := by
  intro p hp hb
  have hbR : (0 : ℝ) < p.1 := by exact_mod_cast (show 0 < p.1 by omega)
  have hn := QRHPowerBounds.numerical_of_power (coefficient_le p.1).1
    (by norm_num : (7 / 8 : ℝ) < 1) hbR (k := 0) (by norm_num) (table_power hpsi p.1 hb)
  constructor
  · simpa only [pow_zero, mul_one,
      show -(1 - (7 / 8 : ℝ)) * (p.1 : ℝ) = -(p.1 : ℝ) / 8 by ring] using hn
  · exact (mul_le_mul_of_nonneg_right (coefficient_le p.1).2 (exp_pos _).le).trans_lt
      (QRHTableReplay.table_updates hpsi p hp hb).2

theorem table8_strict_count :
    (BKLNW.v1.table8.filter (fun p ↦ decide (224 ≤ p.1))).length = 45 := by
  norm_num [BKLNW.v1.table8]

-- Rational, outward-rounded uniform allowance per 1000 log units.
noncomputable def ptR : ℝ := 517 / (10 : ℝ) ^ 57

theorem exp_neg125_upper : exp (-125 : ℝ) ≤ ptR := by
  have he : (2.71828 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp : (2.71828 : ℝ) ^ 125 ≤ exp (125 : ℝ) := by
    convert pow_le_pow_left₀ (by norm_num) he 125 using 1 <;> first | rfl | (rw [← Real.exp_nat_mul]; norm_num)
  rw [Real.exp_neg]
  rw [← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have hr : 0 ≤ ptR := by norm_num [ptR]
  have hm := mul_le_mul_of_nonneg_left hp hr
  norm_num [ptR] at hm ⊢
  linarith

theorem pt_phase2 (hpsi : QRHCH2.v2.psi_density_frontier) (k : ℕ) (hk : 1 ≤ k) :
    HasNumericalBound Eψ (0.01014 * ptR ^ k) (exp (1000 * (k : ℝ))) := by
  have hbase : HasPowerLogBound Eψ 0.01014 0 (7 / 8) (exp (1000 * (k : ℝ))) := by
    intro x hx
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    convert hpsi 1000 0.01014 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr (by nlinarith : (1000 : ℝ) ≤ 1000 * k)).trans hx) using 1 <;> norm_num
  have hkpos : (0 : ℝ) < 1000 * k := by exact_mod_cast (show 0 < 1000 * k by omega)
  have hn := QRHPowerBounds.numerical_of_power (by norm_num : (0 : ℝ) ≤ 0.01014)
    (by norm_num : (7 / 8 : ℝ) < 1) hkpos (k := 0) (by norm_num) hbase
  have he : exp (-(125 : ℝ) * k) ≤ ptR ^ k := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (exp_pos _).le exp_neg125_upper k
  intro x hx
  have hnx := hn x hx
  simp only [pow_zero, mul_one] at hnx
  have heq : -(1 - (7 / 8 : ℝ)) * (1000 * k) = -125 * k := by ring
  rw [heq] at hnx
  exact hnx.trans (mul_le_mul_of_nonneg_left he (by norm_num))

theorem pt_table_strict : ∀ p ∈ PlattTrudgian2021.v1.table1,
    (0.01014 : ℝ) * ptR ^ ⌊p.1 / 1000⌋₊ < p.2.2.2.2 := by
  norm_num [PlattTrudgian2021.v1.table1, ptR]
theorem table8_phase1_strict (b : ℕ) (hb : 224 ≤ b) :
    tableCoefficient b * exp (-(b : ℝ) / 8) < 0.01713 * exp (-(b : ℝ) / 8) := by
  exact mul_lt_mul_of_pos_right (coefficient_strict b hb) (exp_pos _)

end QRHPhase2
