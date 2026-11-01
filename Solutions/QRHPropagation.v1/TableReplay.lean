/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityApplications
import IEANTN.Nodes.BKLNW.v1.Tables

/-! One general replay of the old table thresholds, not one node per row. -/
namespace QRHTableReplay
open Real IEANTN

/-- Exact comparisons against the registered data, not a new citation to the paper. -/
theorem table_min : ∀ p ∈ BKLNW.v1.table8, (7.57240e-50 : ℝ) ≤ p.2 := by
  norm_num [BKLNW.v1.table8]

theorem table_low_min : ∀ p ∈ BKLNW.v1.table8, p.1 < 1000 → (1.95e-12 : ℝ) ≤ p.2 := by
  norm_num [BKLNW.v1.table8]

/-- All 46 old rows at b>=200 receive a smaller certified allowance, valid on a whole ray. -/
theorem table_updates (hpsi : QRHCH2.v2.psi_density_frontier) :
    ∀ p ∈ BKLNW.v1.table8, 200 ≤ p.1 →
      HasNumericalBound Eψ (0.01713 * exp (-(p.1 : ℝ) / 8)) (exp p.1) ∧
        0.01713 * exp (-(p.1 : ℝ) / 8) < p.2 := by
  intro p hp hb
  have hbR : (200 : ℝ) ≤ p.1 := by exact_mod_cast hb
  have hshape : HasPowerLogBound Eψ 0.01713 0 (7 / 8) (exp p.1) := by
    intro x hx
    have h := hpsi 192 0.01713 (by norm_num [CH2.v6.densityFrontier]) x
      ((exp_le_exp.mpr (by linarith : (192 : ℝ) ≤ p.1)).trans hx)
    convert h using 1 <;> norm_num
  have hn := QRHPowerBounds.numerical_of_power (by norm_num : (0 : ℝ) ≤ 0.01713)
    (by norm_num : (7 / 8 : ℝ) < 1) (by linarith : (0 : ℝ) < p.1)
    (k := 0) (by norm_num) hshape
  have heq : -(1 - (7 / 8 : ℝ)) * p.1 = -(p.1 : ℝ) / 8 := by ring
  constructor
  · simpa only [pow_zero, mul_one, heq] using hn
  · by_cases h1000 : 1000 ≤ p.1
    · have hR : (1000 : ℝ) ≤ p.1 := by exact_mod_cast h1000
      have hmono : exp (-(p.1 : ℝ) / 8) ≤ exp (-125) := exp_le_exp.mpr (by linarith)
      have he := QRHPropagation.exp_neg_nat_upper 125
      have hc : (0.01713 : ℝ) * exp (-125) < 7.57240e-50 := by
        calc
          _ ≤ 0.01713 * (10 / 27 : ℝ) ^ 125 :=
            mul_le_mul_of_nonneg_left he (by norm_num)
          _ < _ := by norm_num
      exact ((mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 0.01713)).trans_lt hc).trans_le
        (table_min p hp)
    · have hmono : exp (-(p.1 : ℝ) / 8) ≤ exp (-25) := exp_le_exp.mpr (by linarith)
      have he := QRHPropagation.exp_neg_nat_upper 25
      have hc : (0.01713 : ℝ) * exp (-25) < 1.95e-12 := by
        calc
          _ ≤ 0.01713 * (10 / 27 : ℝ) ^ 25 :=
            mul_le_mul_of_nonneg_left he (by norm_num)
          _ < _ := by norm_num
      exact ((mul_le_mul_of_nonneg_left hmono (by norm_num : (0 : ℝ) ≤ 0.01713)).trans_lt hc).trans_le
        (table_low_min p hp (Nat.lt_of_not_ge h1000))

/-- A finite inventory fact, excluded from propagation counts. -/
theorem improved_row_count :
    (BKLNW.v1.table8.filter (fun p ↦ decide (200 ≤ p.1))).length = 46 := by
  norm_num [BKLNW.v1.table8]

end QRHTableReplay
