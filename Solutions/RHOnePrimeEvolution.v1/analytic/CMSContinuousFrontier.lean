/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSGeometrySharp
import CMSSharperUniform

/-! A genuine continuous real frontier, with the source obstruction and its
whole nonconstant logarithmic term retained. No parameter grid is used. -/
namespace RHOnePrime.CMSContinuous
open Real Set
open RHOnePrime.CMSGeometry RHOnePrime.CMSGeometrySharp
open RHOnePrime.CMSPrime RHOnePrime.CMSOpen RHOnePrime.CMSSharper
set_option maxHeartbeats 0

noncomputable def j : ℝ := 28517 / 25000
noncomputable def coefficient (L : ℝ) : ℝ :=
  (1 - 2 * (log ((399 / 1000 : ℝ) * L) - 117 / 100) / L) / j + 1 / (10000 * L)
noncomputable def upperEndpoint (x : ℝ) : ℝ :=
  x + 2 + coefficient (log (x + 1)) * sqrt (x + 1) * log (x + 1)

lemma log_at_44_upper : log ((399 / 1000 : ℝ) * 44) < 3 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < (399 / 1000) * 44)).mpr
  have he : (8 / 3 : ℝ) < exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_lt_pow_left₀ he (by norm_num : (0 : ℝ) ≤ 8 / 3) (by norm_num : (3 : ℕ) ≠ 0)
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith

lemma log_bound {L : ℝ} (hL : 44 ≤ L) :
    log ((399 / 1000 : ℝ) * L) ≤ 3 + (L - 44) / 44 := by
  have h0 : 0 < L := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos h0 (by norm_num : (0 : ℝ) < 44))
  have he : log ((399 / 1000 : ℝ) * L) - log ((399 / 1000 : ℝ) * 44) = log (L / 44) := by
    rw [Real.log_mul (by norm_num : (399 / 1000 : ℝ) ≠ 0) h0.ne',
      Real.log_mul (by norm_num : (399 / 1000 : ℝ) ≠ 0) (by norm_num), Real.log_div h0.ne' (by norm_num)]
    ring
  have hb := log_at_44_upper
  linarith

lemma coefficient_identity {L : ℝ} (hL : 0 < L) :
    j * coefficient L * L = L - 2 * (log ((399 / 1000 : ℝ) * L) - 117 / 100) + j / 10000 := by
  unfold coefficient j
  field_simp

lemma coefficient_bounds {L : ℝ} (hL : 44 ≤ L) :
    (4 / 5 : ℝ) ≤ coefficient L ∧ coefficient L ≤ 8767 / 10000 := by
  have hL0 : 0 < L := by linarith
  have hj : 0 < j := by norm_num [j]
  have hid := coefficient_identity hL0
  have hlog := log_bound hL
  have hlow : (4 / 5 : ℝ) ≤ coefficient L := by
    apply (mul_le_mul_iff_right₀ hL0).mp
    apply (mul_le_mul_iff_left₀ hj).mp
    unfold j at *
    nlinarith
  have harg : (16 : ℝ) ≤ (399 / 1000 : ℝ) * L := by linarith
  have hmlog := Real.log_le_log (by norm_num : (0 : ℝ) < 16) harg
  have hlog16 : log (16 : ℝ) = 4 * log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog16] at hmlog
  have hupper : coefficient L ≤ 1 / j := by
    apply (le_div_iff₀ hj).mpr
    apply (mul_le_mul_iff_right₀ hL0).mp
    unfold j at *
    nlinarith [Real.log_two_gt_d9]
  refine ⟨hlow,hupper.trans ?_⟩
  norm_num [j]

theorem closed_prime_continuous (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeClosed x (x + coefficient (log x) * sqrt x * log x) := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hx
  obtain ⟨hc,hcub⟩ := coefficient_bounds hL
  have hc1 : coefficient (log x) ≤ 1 := by linarith
  suffices HasPrimeClosed (exp (log x))
      (exp (log x) + coefficient (log x) * sqrt (exp (log x)) * log x) by
    simpa only [Real.exp_log hx0] using this
  by_contra hp
  have hob := hCMS rh (log x) (coefficient (log x)) hL ⟨by linarith,hc1⟩ hp
  have hm0 := mainScale_nonneg hc hc1 hL
  have hm := mainScale_lower hc hc1 hL
  have hz := logScale_tighter hc hc1 hL
  have hmul := mul_le_mul_of_nonneg_right actual_cmsJ_sharper hm0
  have hlow := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 28517 / 25000)
  have hid := coefficient_identity (show 0 < log x by linarith)
  unfold j at hid
  nlinarith

theorem open_prime_continuous (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) : HasPrimeOpen x (upperEndpoint x) := by
  obtain ⟨p,hp,hlo,hhi⟩ := closed_prime_continuous hCMS rh (show exp 44 ≤ x + 1 by linarith)
  refine ⟨p,hp,by linarith,?_⟩
  unfold upperEndpoint
  linarith

/-- The exact variable endpoint is uniformly inside the proved .8768 window. -/
theorem continuous_endpoint_lt_uniform {x : ℝ} (hx : exp 44 ≤ x) :
    upperEndpoint x < x + (548 / 625) * sqrt x * log x := by
  obtain ⟨hs,hl,hx1⟩ := large_width hx
  have hy0 : 0 < x + 1 := by linarith
  have hy : 44 ≤ log (x + 1) := (Real.le_log_iff_exp_le hy0).mpr (by linarith)
  have hc := (coefficient_bounds hy).2
  have hfy : 0 ≤ sqrt (x + 1) * log (x + 1) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hcmul := mul_le_mul_of_nonneg_right hc hfy
  have hshift := sqrt_log_shift hx1
  have hsmul := mul_le_mul_of_nonneg_left hshift (by norm_num : (0 : ℝ) ≤ 8767 / 10000)
  have hroom : log x + 4 < (1 / 10000 : ℝ) * sqrt x * log x := by
    have hp := mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ log x by linarith)
    nlinarith
  unfold upperEndpoint
  nlinarith

theorem continuous_endpoint_lt_CMS {x : ℝ} (hx : exp 44 ≤ x) :
    upperEndpoint x < x + (22 / 25) * sqrt x * log x := by
  have h := continuous_endpoint_lt_uniform hx
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  have hL : 44 ≤ log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hm := mul_pos (Real.sqrt_pos.mpr hx0) (show 0 < log x by linarith)
  nlinarith

#print axioms coefficient_bounds
#print axioms closed_prime_continuous
#print axioms open_prime_continuous
#print axioms continuous_endpoint_lt_uniform
#print axioms continuous_endpoint_lt_CMS
#check @open_prime_continuous
end RHOnePrime.CMSContinuous
