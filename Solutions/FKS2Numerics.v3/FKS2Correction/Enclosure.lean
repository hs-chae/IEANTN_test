/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Correction.Source300

namespace FKS2Correction
open FKS2Scalar

def uLo : Rat := 136218335770 / 10 ^ 12
def uHi : Rat := 136218335771 / 10 ^ 12
def zLo : Rat := 7341155611290 / 10 ^ 12
def zHi : Rat := 7341155611291 / 10 ^ 12

def nuLo : Rat :=
  (1 / 121.096) * uLo ^ 3 * expLo (2 * zLo) *
    ((1 + 1.93378e-8) * 300 * (expLo (-15)) ^ 10 +
      ((1 + 1.93378e-8) * max s1lo s2lo) * 300 * (expLo (-20)) ^ 10)
def nuHi : Rat :=
  (1 / 121.096) * uHi ^ 3 * expHi (2 * zHi) *
    ((1 + 1.93378e-8) * 300 * (expHi (-15)) ^ 10 +
      ((1 + 1.93378e-8) * max s1hi s2hi) * 300 * (expHi (-20)) ^ 10)

theorem root_bounds :
    (uLo : ℝ) ≤ Real.sqrt (5.5666305 / 300) ∧
    Real.sqrt (5.5666305 / 300) ≤ (uHi : ℝ) ∧
    (zLo : ℝ) ≤ Real.sqrt (300 / 5.5666305) ∧
    Real.sqrt (300 / 5.5666305) ≤ (zHi : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    norm_num [uLo]
  · apply Real.sqrt_le_iff.mpr
    norm_num [uHi]
  · apply Real.le_sqrt_of_sq_le
    norm_num [zLo]
  · apply Real.sqrt_le_iff.mpr
    norm_num [zHi]

theorem z_exp_checks :
    expCheck (2 * zLo) (expLo (2 * zLo)) (expHi (2 * zLo)) = true ∧
    expCheck (2 * zHi) (expLo (2 * zHi)) (expHi (2 * zHi)) = true ∧
    expCheck (-15) (expLo (-15)) (expHi (-15)) = true ∧
    expCheck (-20) (expLo (-20)) (expHi (-20)) = true := by
  native_decide

theorem target_enclosure : (nuLo : ℝ) ≤ FKS2Numerics.v3.nuStar 121.096 300 ∧ FKS2Numerics.v3.nuStar 121.096 300 ≤ (nuHi : ℝ) := by
  have hs1 := sum1_bounds
  have hs2 := sum2_bounds
  have hr := root_bounds
  have he15 := expCheck_sound z_exp_checks.2.2.1
  have he20 := expCheck_sound z_exp_checks.2.2.2
  simp only [Rat.cast_neg, Rat.cast_ofNat] at he15 he20
  have heL := (expCheck_sound z_exp_checks.1).1
  have heU := (expCheck_sound z_exp_checks.2.1).2
  simp only [Rat.cast_mul, Rat.cast_ofNat] at heL heU
  have hzL : (expLo (2 * zLo) : ℝ) ≤ Real.exp (2 * Real.sqrt (300 / 5.5666305)) :=
    heL.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2.2.1 (by norm_num)))
  have hzU : Real.exp (2 * Real.sqrt (300 / 5.5666305)) ≤ (expHi (2 * zHi) : ℝ) :=
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr.2.2.2 (by norm_num))).trans heU
  have hc : (0 : Rat) ≤ uLo ∧ 0 ≤ expLo (2 * zLo) ∧ 0 ≤ expLo (-15) ∧
      0 ≤ expLo (-20) ∧ 0 ≤ s1lo ∧ 0 ≤ s2lo := by native_decide
  have hn0 : (0 : ℝ) ≤ (uLo : ℝ) := by exact_mod_cast hc.1
  have hn1 : (0 : ℝ) ≤ (expLo (2 * zLo) : ℝ) := by exact_mod_cast hc.2.1
  have hn2 : (0 : ℝ) ≤ (expLo (-15) : ℝ) := by exact_mod_cast hc.2.2.1
  have hn3 : (0 : ℝ) ≤ (expLo (-20) : ℝ) := by exact_mod_cast hc.2.2.2.1
  have hn4 : (0 : ℝ) ≤ (s1lo : ℝ) := by exact_mod_cast hc.2.2.2.2.1
  have hn5 : (0 : ℝ) ≤ (s2lo : ℝ) := by exact_mod_cast hc.2.2.2.2.2
  have hsum1 : (0 : ℝ) ≤ sum1 := hn4.trans hs1.1
  have hsum2 : (0 : ℝ) ≤ sum2 := hn5.trans hs2.1
  have hnu : (0 : ℝ) ≤ (uHi : ℝ) := (Real.sqrt_nonneg _).trans hr.2.1
  have hne : (0 : ℝ) ≤ (expHi (2 * zHi) : ℝ) := (Real.exp_nonneg _).trans hzU
  have hns1 : (0 : ℝ) ≤ (s1hi : ℝ) := hsum1.trans hs1.2
  have hns2 : (0 : ℝ) ≤ (s2hi : ℝ) := hsum2.trans hs2.2
  rw [target_normalization (by norm_num)]
  have h15 : Real.exp (-(300 : ℝ) / 2) = Real.exp (-15) ^ (10 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  have h20 : Real.exp (-2 * (300 : ℝ) / 3) = Real.exp (-20) ^ (10 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [normalizedTarget, h15, h20]
  unfold nuLo nuHi
  push_cast
  constructor
  · gcongr
    all_goals
      first
      | exact hr.1
      | exact hzL
      | exact he15.1
      | exact he20.1
      | exact hs1.1
      | exact hs2.1
  · gcongr
    all_goals
      first
      | exact hr.2.1
      | exact hzU
      | exact he15.2
      | exact he20.2
      | exact hs1.2
      | exact hs2.2

end FKS2Correction
