/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSGeometrySharp
import CMSOpenTransfer

/-! A stronger finite slab from recovered logarithmic geometry. -/
namespace RHOnePrime.CMSTight
open Real Set
open RHOnePrime.CMSGeometry RHOnePrime.CMSGeometrySharp
open RHOnePrime.CMSScalar RHOnePrime.CMSPrime RHOnePrime.CMSOpen
set_option maxHeartbeats 0

noncomputable def tightMargin (c L : ℝ) : ℝ :=
  log ((399 / 1000 : ℝ) * L) - effectiveCost c * L - 117 / 100

lemma logarithm_2394_lower : (317 / 100 : ℝ) < log (1197 / 50) := by
  have h := Real.le_log_one_add_of_nonneg (x := (397 / 800 : ℝ)) (by norm_num)
  norm_num at h
  have he : log (1197 / 50 : ℝ) = 4 * log 2 + log (1197 / 800) := by
    rw [show (1197 / 50 : ℝ) = 2 ^ (4 : ℕ) * (1197 / 800) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (4 : ℕ) ≠ 0) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

lemma tight_slab_08184 {L : ℝ} (hlo : 44 ≤ L) (hhi : L ≤ 60) :
    0 < tightMargin (1023 / 1250) L := by
  have hmono := log_sub_linear_antitone (a := (399 / 1000 : ℝ))
    (d := effectiveCost (1023 / 1250)) (by norm_num) (by linarith : 0 < L) hhi
    (by unfold effectiveCost jFloor; nlinarith)
  have hend : 0 < tightMargin (1023 / 1250) 60 := by
    unfold tightMargin effectiveCost jFloor
    norm_num
    linarith [logarithm_2394_lower]
  unfold tightMargin at *
  linarith

lemma closed_from_tight_margin (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {c L : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1) (hL : 44 ≤ L)
    (hmarg : 0 < tightMargin c L) :
    HasPrimeClosed (exp L) (exp L + c * sqrt (exp L) * L) := by
  by_contra hp
  have hob := hCMS rh L c hL ⟨by linarith,hc1⟩ hp
  have hm0 := mainScale_nonneg hc hc1 hL
  have hm := mainScale_lower hc hc1 hL
  have hz := logScale_tighter hc hc1 hL
  have hJ := mul_le_mul_of_nonneg_right RHOnePrimeEvolution.CMSNumerics.actual_cmsJ_lower hm0
  have hl := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 2281 / 2000)
  unfold tightMargin effectiveCost jFloor at hmarg
  nlinarith

theorem closed_prime_08184 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 60) :
    HasPrimeClosed x (x + (1023 / 1250) * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hlo
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hlo
  have hU : log x ≤ 60 := (Real.log_le_iff_le_exp hx0).mpr hhi
  have h := closed_from_tight_margin hCMS rh (by norm_num : (4 / 5 : ℝ) ≤ 1023 / 1250)
    (by norm_num) hL (tight_slab_08184 hL hU)
  simpa only [Real.exp_log hx0] using h

theorem open_prime_08185 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 59) :
    HasPrimeOpen x (x + (1637 / 2000) * sqrt x * log x) := by
  have hylo : exp 44 ≤ x + 1 := by linarith
  have hyhi : x + 1 ≤ exp 60 := by
    have h := shift_below_next_exp (by norm_num : (0 : ℝ) ≤ 59) hhi
    norm_num at h
    exact h
  have h := open_of_shifted_closed (by norm_num : (0 : ℝ) ≤ 1023 / 1250)
    (by norm_num) hlo (closed_prime_08184 hCMS rh hylo hyhi)
  norm_num at h ⊢
  exact h

#print axioms logarithm_2394_lower
#print axioms tight_slab_08184
#print axioms closed_prime_08184
#print axioms open_prime_08185
#check @open_prime_08185
end RHOnePrime.CMSTight
