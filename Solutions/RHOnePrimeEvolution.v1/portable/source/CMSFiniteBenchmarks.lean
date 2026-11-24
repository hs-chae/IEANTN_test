/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSTightSlab

/-! Matched finite-domain benchmark comparisons, not asymptotic records. -/
namespace RHOnePrime.CMSFinite
open Real Set
open RHOnePrime.CMSScalar RHOnePrime.CMSPrime RHOnePrime.CMSOpen RHOnePrime.CMSTight
set_option maxHeartbeats 0

lemma log44_lower : (189 / 50 : ℝ) < log 44 := by
  have h := Real.le_log_one_add_of_nonneg (x := (3 / 8 : ℝ)) (by norm_num)
  norm_num at h
  have he : log (44 : ℝ) = 5 * log 2 + log (11 / 8) := by
    rw [show (44 : ℝ) = 2 ^ (5 : ℕ) * (11 / 8) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (5 : ℕ) ≠ 0) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

lemma log90_lower : (449 / 100 : ℝ) < log 90 := by
  have h := Real.le_log_one_add_of_nonneg (x := (13 / 32 : ℝ)) (by norm_num)
  norm_num at h
  have he : log (90 : ℝ) = 6 * log 2 + log (45 / 32) := by
    rw [show (90 : ℝ) = 2 ^ (6 : ℕ) * (45 / 32) by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ^ (6 : ℕ) ≠ 0) (by norm_num), Real.log_pow]
    norm_num
  rw [he]
  linarith [Real.log_two_gt_d9]

lemma positive_tight_slab {c A B L : ℝ} (hA : 0 < A) (hlo : A ≤ L) (hhi : L ≤ B)
    (hd : 1 ≤ effectiveCost c * A) (hend : 0 < tightMargin c B) :
    0 < tightMargin c L := by
  have hd0 : 0 ≤ effectiveCost c := by nlinarith
  have hdL : 1 ≤ effectiveCost c * L := by nlinarith
  have hmono := log_sub_linear_antitone (a := (399 / 1000 : ℝ))
    (d := effectiveCost c) (by norm_num) (hA.trans_le hlo) hhi hdL
  unfold tightMargin at *
  linarith

lemma margin_08356 {L : ℝ} (hlo : 44 ≤ L) (hhi : L ≤ 111) :
    0 < tightMargin (2089 / 2500) L := by
  apply positive_tight_slab (A := 44) (B := 111) (by norm_num) hlo hhi
  · norm_num [effectiveCost,jFloor]
  · have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 44)
      (by norm_num : (44 : ℝ) ≤ (399 / 1000) * 111)
    unfold tightMargin effectiveCost jFloor
    norm_num
    linarith [log44_lower]

lemma tight_mono_coefficient {c d L : ℝ} (hcd : c ≤ d) (hL : 0 ≤ L) :
    tightMargin c L ≤ tightMargin d L := by
  have hm := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2281 / 2000)
    (sub_nonneg.mpr hcd)) hL
  unfold tightMargin effectiveCost jFloor
  nlinarith

lemma margin_08511 {L : ℝ} (hlo : 44 ≤ L) (hhi : L ≤ 226) :
    0 < tightMargin (8511 / 10000) L := by
  by_cases hmid : L ≤ 111
  · exact (margin_08356 hlo hmid).trans_le (tight_mono_coefficient (by norm_num) (by linarith))
  · apply positive_tight_slab (A := 111) (B := 226) (by norm_num) (by linarith) hhi
    · norm_num [effectiveCost,jFloor]
    · have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 90)
        (by norm_num : (90 : ℝ) ≤ (399 / 1000) * 226)
      unfold tightMargin effectiveCost jFloor
      norm_num
      linarith [log90_lower]

lemma closed_capped (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {c B x : ℝ} (hc : (4 / 5 : ℝ) ≤ c) (hc1 : c ≤ 1)
    (hmargin : ∀ L : ℝ, 44 ≤ L → L ≤ B → 0 < tightMargin c L)
    (hlo : exp 44 ≤ x) (hhi : x ≤ exp B) :
    HasPrimeClosed x (x + c * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hlo
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hlo
  have hU : log x ≤ B := (Real.log_le_iff_le_exp hx0).mpr hhi
  have h := closed_from_tight_margin hCMS rh hc hc1 hL (hmargin _ hL hU)
  simpa only [Real.exp_log hx0] using h

theorem open_prime_08357 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 110) :
    HasPrimeOpen x (x + (8357 / 10000) * sqrt x * log x) := by
  have hylo : exp 44 ≤ x + 1 := by linarith
  have hyhi : x + 1 ≤ exp 111 := by
    have h := shift_below_next_exp (by norm_num : (0 : ℝ) ≤ 110) hhi
    norm_num at h; exact h
  have hc := closed_capped hCMS rh (c := (2089 / 2500 : ℝ)) (B := 111)
    (by norm_num) (by norm_num) (fun L hL hB => margin_08356 hL hB) hylo hyhi
  have h := open_of_shifted_closed (by norm_num : (0 : ℝ) ≤ 2089 / 2500) (by norm_num) hlo hc
  norm_num at h ⊢
  exact h

theorem open_prime_08512 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 225) :
    HasPrimeOpen x (x + (532 / 625) * sqrt x * log x) := by
  have hylo : exp 44 ≤ x + 1 := by linarith
  have hyhi : x + 1 ≤ exp 226 := by
    have h := shift_below_next_exp (by norm_num : (0 : ℝ) ≤ 225) hhi
    norm_num at h; exact h
  have hc := closed_capped hCMS rh (c := (8511 / 10000 : ℝ)) (B := 226)
    (by norm_num) (by norm_num) (fun L hL hB => margin_08511 hL hB) hylo hyhi
  have h := open_of_shifted_closed (by norm_num : (0 : ℝ) ≤ 8511 / 10000) (by norm_num) hlo hc
  norm_num at h ⊢
  exact h

#print axioms open_prime_08357
#print axioms open_prime_08512
#check @open_prime_08357
#check @open_prime_08512
end RHOnePrime.CMSFinite
