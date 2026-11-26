/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMontgomeryVaughan
import ExplicitPrimeWeights
import ExplicitResidual

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Explicit

/-- The actual half-open central prime sum, with the same phase L=t+d and
von-Mangoldt weight as in the proved Mellin identity. -/
def centralPrimeSum (nodes : List ℚ) (m : ℕ) (d t : ℝ) : ℝ :=
  ∑ p ∈ realPrimesIoc (exp t) (exp (t+2*d)),
    (ArithmeticFunction.vonMangoldt p:ℝ)*mellinArithmeticWeight nodes m d (t+d) p

theorem centralPrimeSum_le_count (nodes : List ℚ) (m : ℕ) (d t M : ℝ)
    (ht : 2 ≤ t) (hd : 0 ≤ d) (hM : 0 ≤ M)
    (hW : ∀ v : ℝ, |affineSpectrum nodes m v| ≤ M) :
    centralPrimeSum nodes m d t ≤
      M*t*exp (-t/2)*((realPrimesIoc (exp t) (exp (t+2*d))).card:ℝ) := by
  unfold centralPrimeSum
  calc
    _ ≤ ∑ _p ∈ realPrimesIoc (exp t) (exp (t+2*d)), M*t*exp (-t/2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hm := (mem_realPrimesIoc (exp t) (exp (t+2*d)) (exp_pos _).le (exp_pos _).le p).mp hp
      have h := interior_prime_term_le nodes m d (t+d) M t hM hW ht
        (⟨p,hm.1.two_le⟩ : CMSPrimeIndex) hm.1 hm.2.1.le
      exact h
    _ = _ := by simp [mul_comm]

/-- More than one actual half-open prime suffices to delete a possible
upper-endpoint prime. This covers nonintegral endpoints as well. -/
theorem strict_prime_of_two_halfopen (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcount : 2 ≤ (realPrimesIoc a b).card) :
    ∃ p : ℕ, Nat.Prime p ∧ a < (p:ℝ) ∧ (p:ℝ) < b := by
  by_contra hh
  push_neg at hh
  have hcard : (realPrimesIoc a b).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    have hpm := (mem_realPrimesIoc a b ha hb p).mp hp
    have hqm := (mem_realPrimesIoc a b ha hb q).mp hq
    have hpe : (p:ℝ) = b := le_antisymm hpm.2.2 (hh p hpm.1 hpm.2.1)
    have hqe : (q:ℝ) = b := le_antisymm hqm.2.2 (hh q hqm.1 hqm.2.1)
    exact_mod_cast hpe.trans hqe.symm
  omega

/-- A genuine central-sum lower bound is consumed to prove the final STRICT
prime interval. There is no upper-endpoint assumption about the input. -/
theorem strict_prime_of_central_lower (nodes : List ℚ) (m : ℕ) (d t M r : ℝ)
    (ht : 42 ≤ t) (hd : 0 ≤ d) (hM : 0 ≤ M) (hM2 : M ≤ 2)
    (hW : ∀ v : ℝ, |affineSpectrum nodes m v| ≤ M)
    (hr : (1/1000000:ℝ) ≤ r) (hLower : r ≤ centralPrimeSum nodes m d t) :
    ∃ p : ℕ, Nat.Prime p ∧ exp t < (p:ℝ) ∧ (p:ℝ) < exp (t+2*d) := by
  have hCount := centralPrimeSum_le_count nodes m d t M (by linarith) hd hM hW
  have hh := count_gt_one_of_residual t M
    ((realPrimesIoc (exp t) (exp (t+2*d))).card:ℝ) r ht hM hM2 hr (hLower.trans hCount)
  have hn : 2 ≤ (realPrimesIoc (exp t) (exp (t+2*d))).card := by
    have : 1 < (realPrimesIoc (exp t) (exp (t+2*d))).card := by exact_mod_cast hh
    omega
  exact strict_prime_of_two_halfopen _ _ (exp_pos _).le (exp_pos _).le hn

/-- The logarithmic window parameter gives exactly the intended rightward
prime interval, including its literal length normalization. -/
theorem central_right_endpoint (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (ht : 42 ≤ t) :
    exp (t+2*halfLogWidth c t) = exp t+c*sqrt (exp t)*log (exp t) := by
  have hz := intervalRatio_pos c t hc ht
  unfold halfLogWidth
  rw [show 2*(log (1+intervalRatio c t)/2) = log (1+intervalRatio c t) by ring,
    exp_add,exp_log (by linarith : 0 < 1+intervalRatio c t),log_exp,←exp_half]
  unfold intervalRatio
  have he : exp t*exp (-t/2) = exp (t/2) := by rw [←exp_add]; congr 1; ring
  calc
    _ = exp t+c*t*(exp t*exp (-t/2)) := by ring
    _ = _ := by rw [he]; ring

#print axioms centralPrimeSum_le_count
#print axioms strict_prime_of_central_lower
#print axioms central_right_endpoint
end RH080Next.Explicit
