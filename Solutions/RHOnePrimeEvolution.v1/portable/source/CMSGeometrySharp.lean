/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSGeometry

/-! Recover the small-scale logarithmic loss in the earlier source adapter.
The physical kernel and the literature premise are unchanged. -/
namespace RHOnePrime.CMSGeometrySharp
open Real
open RHOnePrime.CMSGeometry
set_option maxHeartbeats 0

lemma ratio_very_small {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : ratio c L ≤ 1 / 1000 := by
  have hE := exp_dominates hL
  have hC := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ L by linarith)
  unfold ratio
  apply (div_le_iff₀ (exp_pos _)).mpr
  nlinarith

lemma halfLogSpan_tighter {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : (399 / 1000 : ℝ) * L / exp (L / 2) ≤ halfLogSpan c L := by
  have hr0 := (ratio_bounds hc hc1 hL).1
  have hr1 := ratio_very_small hc hc1 hL
  have ht := Real.le_log_one_add_of_nonneg hr0.le
  have hfrac : (399 / 800 : ℝ) * ratio c L ≤ ratio c L / (ratio c L + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < ratio c L + 2)).mpr
    nlinarith
  have hr : (4 / 5 : ℝ) * L / exp (L / 2) ≤ ratio c L := by
    unfold ratio
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by linarith)) (exp_pos _).le
  unfold halfLogSpan
  calc
    (399 / 1000 : ℝ) * L / exp (L / 2) =
        (399 / 800 : ℝ) * ((4 / 5 : ℝ) * L / exp (L / 2)) := by ring
    _ ≤ (399 / 800 : ℝ) * ratio c L := mul_le_mul_of_nonneg_left hr (by norm_num)
    _ ≤ ratio c L / (ratio c L + 2) := hfrac
    _ ≤ log (1 + ratio c L) / 2 := by
      have he : 2 * ratio c L / (ratio c L + 2) = 2 * (ratio c L / (ratio c L + 2)) := by ring
      rw [he] at ht
      linarith

lemma logScale_tighter {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hL : 44 ≤ L) : logScale c L ≤ L / 2 - log ((399 / 1000 : ℝ) * L) := by
  have hlo := halfLogSpan_tighter hc hc1 hL
  have ht := halfLogSpan_pos hc hc1 hL
  have hbase : 0 < (399 / 1000 : ℝ) * L := by positivity
  have hm := Real.log_le_log (div_pos hbase (exp_pos _)) hlo
  rw [Real.log_div hbase.ne' (exp_ne_zero _), Real.log_exp] at hm
  unfold logScale
  rw [Real.log_div one_ne_zero ht.ne', Real.log_one]
  linarith

#print axioms ratio_very_small
#print axioms halfLogSpan_tighter
#print axioms logScale_tighter
end RHOnePrime.CMSGeometrySharp
