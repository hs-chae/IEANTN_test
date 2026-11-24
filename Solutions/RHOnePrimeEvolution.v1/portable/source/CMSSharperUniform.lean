/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSJSharper
import CMSOpenTransfer

/-! A stable stronger uniform theorem from the identical CMS source predicate.
Original .877/.8771 consumers are preserved. -/
namespace RHOnePrime.CMSSharper
open Real Set
open RHOnePrime.CMSGeometry RHOnePrime.CMSScalar RHOnePrime.CMSPrime RHOnePrime.CMSOpen
set_option maxHeartbeats 0

lemma logarithmic_room {L : ℝ} (hL : 44 ≤ L) :
    (117 / 100 : ℝ) < log ((4 / 15 : ℝ) * L) := by
  have harg : (8 : ℝ) ≤ (4 / 15 : ℝ) * L := by linarith
  have hmono := Real.log_le_log (by norm_num : (0 : ℝ) < 8) harg
  have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [he] at hmono
  linarith [Real.log_two_gt_d9]

theorem closed_prime_08767 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeClosed x (x + (8767 / 10000) * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hx
  suffices HasPrimeClosed (exp (log x))
      (exp (log x) + (8767 / 10000) * sqrt (exp (log x)) * log x) by
    simpa only [Real.exp_log hx0] using this
  by_contra hp
  have hob := hCMS rh (log x) (8767 / 10000) hL ⟨by norm_num,by norm_num⟩ hp
  have hm0 := mainScale_nonneg (by norm_num : (4 / 5 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hL
  have hm := mainScale_lower (by norm_num : (4 / 5 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hL
  have hz := logScale_upper (by norm_num : (4 / 5 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hL
  have hroom := logarithmic_room hL
  have hmul := mul_le_mul_of_nonneg_right actual_cmsJ_sharper hm0
  have hlow := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 28517 / 25000)
  norm_num at *
  nlinarith

theorem open_prime_08768 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeOpen x (x + (548 / 625) * sqrt x * log x) := by
  have hy : exp 44 ≤ x + 1 := by linarith
  have h := open_of_shifted_closed (by norm_num : (0 : ℝ) ≤ 8767 / 10000)
    (by norm_num) hx (closed_prime_08767 hCMS rh hy)
  norm_num at h ⊢
  exact h

#print axioms closed_prime_08767
#print axioms open_prime_08768
#check @open_prime_08768
end RHOnePrime.CMSSharper
