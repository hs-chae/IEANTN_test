/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IEANTN contributors
-/
import CMSPrimeFrontier

/-! A genuine endpoint transfer: apply the closed theorem at x+1 and spend
1/10000 of the length coefficient to put BOTH prime endpoints strictly inside
the requested interval. No closed-source no-prime premise is silently opened. -/
namespace RHOnePrime.CMSOpen
open Real Set
open RHOnePrime.CMSPrime
set_option maxHeartbeats 0

def HasPrimeOpen (x y : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) < y

lemma sqrt_log_shift {x : ℝ} (hx : 1 ≤ x) :
    sqrt (x + 1) * log (x + 1) ≤ sqrt x * log x + log x + 2 := by
  have hx0 : 0 < x := by linarith
  have hx10 : 0 < x + 1 := by linarith
  have hs : sqrt (x + 1) ≤ sqrt x + 1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg x]
  have hl : log (x + 1) ≤ log x + 1 / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx10 hx0)
    rw [Real.log_div hx10.ne' hx0.ne'] at h
    have he : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rw [he] at h
    linarith
  have hl0 : 0 ≤ log (x + 1) := Real.log_nonneg (by linarith)
  have hm := mul_le_mul hs hl hl0 (by positivity : 0 ≤ sqrt x + 1)
  have hroot : sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx)
  have hr : (sqrt x + 1) / x ≤ 2 := by
    apply (div_le_iff₀ hx0).mpr
    linarith
  have he : (sqrt x + 1) * (log x + 1 / x) =
      sqrt x * log x + log x + (sqrt x + 1) / x := by ring
  rw [he] at hm
  linarith

lemma large_width {x : ℝ} (hx : exp 44 ≤ x) :
    (100000 : ℝ) ≤ sqrt x ∧ 44 ≤ log x ∧ 1 ≤ x := by
  have hx0 : 0 < x := (exp_pos 44).trans_le hx
  have he := Real.pow_div_factorial_le_exp (22 : ℝ) (by norm_num) 6
  norm_num at he
  have hs := Real.sqrt_le_sqrt hx
  have heq : (exp (22 : ℝ)) ^ 2 = exp 44 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hroot : sqrt (exp (44 : ℝ)) = exp 22 := by
    rw [← heq, Real.sqrt_sq (exp_pos _).le]
  rw [hroot] at hs
  refine ⟨by linarith, (Real.le_log_iff_exp_le hx0).mpr hx, ?_⟩
  exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 44)).trans hx

lemma shifted_window_strictly_inside {c x : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hx : exp 44 ≤ x) :
    x + 1 + c * sqrt (x + 1) * log (x + 1) <
      x + (c + 1 / 10000) * sqrt x * log x := by
  obtain ⟨hs,hl,hx1⟩ := large_width hx
  have hm := sqrt_log_shift hx1
  have hmul := mul_le_mul_of_nonneg_left hm hc
  have hcost : c * (log x + 2) ≤ log x + 2 := by
    nlinarith
  have hroom : log x + 3 < (1 / 10000 : ℝ) * sqrt x * log x := by
    have hp := mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ log x by linarith)
    nlinarith
  nlinarith

lemma open_of_shifted_closed {c x : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hx : exp 44 ≤ x)
    (hprime : HasPrimeClosed (x + 1) (x + 1 + c * sqrt (x + 1) * log (x + 1))) :
    HasPrimeOpen x (x + (c + 1 / 10000) * sqrt x * log x) := by
  obtain ⟨p,hp,hlo,hhi⟩ := hprime
  refine ⟨p,hp,by linarith, hhi.trans_lt (shifted_window_strictly_inside hc hc1 hx)⟩

/-- Same published analytic source package, with the endpoint loss PROVED.
The coefficient is genuinely below .88; its comparison is to the rounded
published theorem, not a claim that CMS lacked the latent sharper constant. -/
theorem open_prime_08771 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hx : exp 44 ≤ x) :
    HasPrimeOpen x (x + (8771 / 10000) * sqrt x * log x) := by
  have hy : exp 44 ≤ x + 1 := by linarith
  have h := open_of_shifted_closed (by norm_num : (0 : ℝ) ≤ 877 / 1000)
    (by norm_num) hx (closed_prime_0877 hCMS rh hy)
  norm_num at h ⊢
  exact h

lemma shift_below_next_exp {B x : ℝ} (hB : 0 ≤ B) (hx : x ≤ exp B) :
    x + 1 ≤ exp (B + 1) := by
  have he : (2 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
  have hE : 1 ≤ exp B := Real.one_le_exp hB
  rw [Real.exp_add]
  nlinarith

/-- A bounded explicit coefficient below .8358, retaining distinct closed
internal and strict-open reported intervals; this is not an asymptotic claim. -/
theorem open_prime_08301 (hCMS : SourceCMS616) (rh : RiemannHypothesis)
    {x : ℝ} (hlo : exp 44 ≤ x) (hhi : x ≤ exp 59) :
    HasPrimeOpen x (x + (8301 / 10000) * sqrt x * log x) := by
  have hylo : exp 44 ≤ x + 1 := by linarith
  have hyhi : x + 1 ≤ exp 60 := by
    have h := shift_below_next_exp (by norm_num : (0 : ℝ) ≤ 59) hhi
    norm_num at h
    exact h
  have h := open_of_shifted_closed (by norm_num : (0 : ℝ) ≤ 83 / 100)
    (by norm_num) hlo (closed_prime_083 hCMS rh hylo hyhi)
  norm_num at h ⊢
  exact h

#print axioms sqrt_log_shift
#print axioms large_width
#print axioms shifted_window_strictly_inside
#print axioms open_prime_08771
#print axioms open_prime_08301
#check @open_prime_08771
#check @open_prime_08301
end RHOnePrime.CMSOpen
