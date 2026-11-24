/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSScalarFrontier

/-! Exact real geometry of the CMS logarithmic window, independent of any
number-theoretic source proposition. -/
namespace RHOnePrime.CMSGeometry
open Real
set_option maxHeartbeats 0

noncomputable def ratio (c L : ℝ) : ℝ := c * L / exp (L / 2)
noncomputable def halfLogSpan (c L : ℝ) : ℝ := log (1 + ratio c L) / 2
noncomputable def mainScale (c L : ℝ) : ℝ :=
  exp ((L + halfLogSpan c L) / 2) * halfLogSpan c L
noncomputable def logScale (c L : ℝ) : ℝ := log (1 / halfLogSpan c L)

lemma exp_dominates {L : ℝ} (hL : 44 ≤ L) : 250 * L ^ 2 ≤ exp (L / 2) := by
  have ht : (22 : ℝ) ≤ L / 2 := by linarith
  have ht0 : (0 : ℝ) ≤ L / 2 := by linarith
  have h6 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 22) ht 6
  have h8 := Real.pow_div_factorial_le_exp (L / 2) ht0 8
  norm_num at h8
  have he : (40320000 : ℝ) ≤ (L / 2) ^ 6 := by norm_num at h6; linarith
  have hm := mul_le_mul_of_nonneg_right he (sq_nonneg (L / 2))
  have hid : (L / 2) ^ 6 * (L / 2) ^ 2 = (L / 2) ^ 8 := by ring
  rw [hid] at hm
  nlinarith

lemma ratio_bounds {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : 0 < ratio c L ∧ ratio c L ≤ 1 := by
  have hE := exp_dominates hL
  have hL0 : 0 < L := by linarith
  have hEL : L ≤ exp (L / 2) := by nlinarith
  constructor
  · unfold ratio; positivity
  · unfold ratio
    apply (div_le_iff₀ (exp_pos _)).mpr
    nlinarith

lemma halfLogSpan_pos {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : 0 < halfLogSpan c L := by
  have hr := (ratio_bounds hc hc1 hL).1
  unfold halfLogSpan
  exact div_pos (Real.log_pos (by linarith)) (by norm_num)

lemma halfLogSpan_lower {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : (4 / 15 : ℝ) * L / exp (L / 2) ≤ halfLogSpan c L := by
  obtain ⟨hr0,hr1⟩ := ratio_bounds hc hc1 hL
  have ht := Real.le_log_one_add_of_nonneg hr0.le
  have hfrac : (2 / 3 : ℝ) * ratio c L ≤ 2 * ratio c L / (ratio c L + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < ratio c L + 2)).mpr
    nlinarith
  have hr : (4 / 5 : ℝ) * L / exp (L / 2) ≤ ratio c L := by
    unfold ratio
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by linarith)) (exp_pos _).le
  unfold halfLogSpan
  calc
    (4 / 15 : ℝ) * L / exp (L / 2) = ((4 / 5 : ℝ) * L / exp (L / 2)) / 3 := by ring
    _ ≤ ratio c L / 3 := div_le_div_of_nonneg_right hr (by norm_num)
    _ ≤ log (1 + ratio c L) / 2 := by linarith

lemma logScale_upper {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : logScale c L ≤ L / 2 - log ((4 / 15 : ℝ) * L) := by
  have hlo := halfLogSpan_lower hc hc1 hL
  have ht := halfLogSpan_pos hc hc1 hL
  have hbase : 0 < (4 / 15 : ℝ) * L := by positivity
  have hm := Real.log_le_log (div_pos hbase (exp_pos _)) hlo
  rw [Real.log_div hbase.ne' (exp_ne_zero _), Real.log_exp] at hm
  unfold logScale
  rw [Real.log_div one_ne_zero ht.ne', Real.log_one]
  linarith

lemma mainScale_nonneg {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : 0 ≤ mainScale c L := by
  unfold mainScale
  exact mul_nonneg (exp_pos _).le (halfLogSpan_pos hc hc1 hL).le

lemma mainScale_lower {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : c * L / 2 - 1 / 1000 ≤ mainScale c L := by
  obtain ⟨hr0,hr1⟩ := ratio_bounds hc hc1 hL
  have ht := Real.le_log_one_add_of_nonneg hr0.le
  have hfrac : ratio c L - (ratio c L) ^ 2 / 2 ≤
      2 * ratio c L / (ratio c L + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < ratio c L + 2)).mpr
    nlinarith [pow_nonneg hr0.le 3]
  have htheta : ratio c L / 2 - (ratio c L) ^ 2 / 4 ≤ halfLogSpan c L := by
    unfold halfLogSpan
    linarith
  have ht0 := (halfLogSpan_pos hc hc1 hL).le
  have hscale : exp (L / 2) ≤ exp ((L + halfLogSpan c L) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hm1 := mul_le_mul_of_nonneg_right hscale ht0
  have hm2 := mul_le_mul_of_nonneg_left htheta (exp_pos (L / 2)).le
  have heq : exp (L / 2) * (ratio c L / 2 - (ratio c L) ^ 2 / 4) =
      c * L / 2 - c ^ 2 * L ^ 2 / (4 * exp (L / 2)) := by
    unfold ratio
    field_simp
  have hE := exp_dominates hL
  have hc0 : 0 ≤ c := by linarith
  have hcsq : c ^ 2 ≤ 1 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hcsq (sq_nonneg L)
  have herr : c ^ 2 * L ^ 2 / (4 * exp (L / 2)) ≤ 1 / 1000 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * exp (L / 2))).mpr
    nlinarith
  rw [heq] at hm2
  unfold mainScale
  linarith

#print axioms exp_dominates
#print axioms ratio_bounds
#print axioms halfLogSpan_pos
#print axioms halfLogSpan_lower
#print axioms logScale_upper
#print axioms mainScale_lower
end RHOnePrime.CMSGeometry
