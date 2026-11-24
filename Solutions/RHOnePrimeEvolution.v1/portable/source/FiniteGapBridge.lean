/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib

/-! Real-uniform transfer from a genuine finite consecutive-prime gap contract.
This module proves the transfer, not the external historical gap computation.
A fixed terminal prime is separate from the consecutive-gap source input.
-/
namespace RHOnePrime.FiniteGap
open Real Finset
set_option maxHeartbeats 0

/-- Standard finite consecutive-prime gap statement: BOTH endpoints are prime,
the upper endpoint is at mostQ, and no prime lies strictly between them.
This is not defined in terms of the desired real interval theorem. -/
def ConsecutiveGapBound (Q G : ℕ) : Prop := ∀ p q : ℕ,
  p.Prime → q.Prime → p < q → q ≤ Q →
  (∀ r : ℕ, p < r → r < q → ¬r.Prime) → q - p ≤ G

/-- Every real x between2 and a terminal prime is bracketed by actual
consecutive primes bounded byQ. The use of floor handles every real point. -/
theorem real_bracketing_primes {Q : ℕ} (hQ : Q.Prime) {x : ℝ}
    (hx : 2 ≤ x) (hxQ : x < Q) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p : ℝ) ≤ x ∧ x < q ∧
      p < q ∧ q ≤ Q ∧ (∀ r : ℕ, p < r → r < q → ¬r.Prime) := by
  classical
  let low := Nat.primesLE ⌊x⌋₊
  have hlow : low.Nonempty := by
    refine ⟨2, Nat.mem_primesLE.mpr ⟨Nat.le_floor hx, Nat.prime_two⟩⟩
  let p := low.max' hlow
  have hpm : p ∈ low := Finset.max'_mem low hlow
  have hpprime : p.Prime := (Nat.mem_primesLE.mp hpm).2
  have hpx : (p : ℝ) ≤ x :=
    (by exact_mod_cast (Nat.mem_primesLE.mp hpm).1 : (p : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
      (Nat.floor_le (by linarith : 0 ≤ x))
  let high := (Nat.primesLE Q).filter (fun q : ℕ => x < (q : ℝ))
  have hhigh : high.Nonempty := by
    exact ⟨Q, Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨le_rfl, hQ⟩, hxQ⟩⟩
  let q := high.min' hhigh
  have hqm : q ∈ high := Finset.min'_mem high hhigh
  have hqprime : q.Prime := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hqm).1).2
  have hqQ : q ≤ Q := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hqm).1).1
  have hxq : x < (q : ℝ) := (Finset.mem_filter.mp hqm).2
  have hpq : p < q := by exact_mod_cast hpx.trans_lt hxq
  refine ⟨p, q, hpprime, hqprime, hpx, hxq, hpq, hqQ, ?_⟩
  intro r hpr hrq hrprime
  by_cases hrx : (r : ℝ) ≤ x
  · have hrm : r ∈ low := Nat.mem_primesLE.mpr ⟨Nat.le_floor hrx, hrprime⟩
    have hrp : r ≤ p := Finset.le_max' low r hrm
    omega
  · have hrm : r ∈ high := Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hrq.le.trans hqQ, hrprime⟩, lt_of_not_ge hrx⟩
    have hqr : q ≤ r := Finset.min'_le high r hrm
    omega

/-- Strict endpoint guaranteed by a strictly larger width than the finite gap.
No grid-point-only argument, rounding of x, or terminal gap is hidden. -/
theorem prime_in_real_interval {Q G : ℕ} (hQ : Q.Prime)
    (hgap : ConsecutiveGapBound Q G) {x h : ℝ}
    (hx : 2 ≤ x) (hxQ : x < Q) (hwidth : (G : ℝ) < h) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧ (q : ℝ) < x + h := by
  obtain ⟨p, q, hp, hq, hpx, hxq, hpq, hqQ, hconsec⟩ :=
    real_bracketing_primes hQ hx hxQ
  have hg := hgap p q hp hq hpq hqQ hconsec
  have hgn : q ≤ p + G := by omega
  have hgr : (q : ℝ) ≤ (p : ℝ) + G := by exact_mod_cast hgn
  exact ⟨q, hq, hxq, by linarith⟩

lemma exp24_large : (1000000 : ℝ) < exp 24 := by
  have hpow : (2 : ℝ) ^ 24 < (exp (1 : ℝ)) ^ 24 :=
    pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
  have he : exp (24 : ℝ) = (exp (1 : ℝ)) ^ 24 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 24
  rw [he]
  norm_num at hpow ⊢
  linarith

lemma width_exceeds_1550 {c x : ℝ} (hc : (4 / 5 : ℝ) ≤ c)
    (hx : exp 24 ≤ x) : 1550 < c * sqrt x * log x := by
  have hxlarge : (1000000 : ℝ) < x := exp24_large.trans_le hx
  have hx0 : 0 ≤ x := by linarith
  have hs : 1000 < sqrt x := by nlinarith [sq_sqrt hx0, sqrt_nonneg x]
  have hl : 24 ≤ log x := by simpa using log_le_log (exp_pos 24) hx
  have hm : (800 : ℝ) < c * sqrt x := by nlinarith
  nlinarith

theorem fixed_gap_one_prime {Q : ℕ} (hQ : Q.Prime)
    (hgap : ConsecutiveGapBound Q 1550) {c x : ℝ}
    (hc : (4 / 5 : ℝ) ≤ c) (hx : exp 24 ≤ x) (hxQ : x < Q) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧
      (q : ℝ) < x + c * sqrt x * log x := by
  apply prime_in_real_interval hQ hgap _ hxQ (width_exceeds_1550 hc hx)
  linarith [exp24_large.trans_le hx]

/-- Exact arithmetic inclusion needed by the requested e44 hybrid bridge. -/
lemma exp44_lt_terminal : exp (44 : ℝ) < (18446744073709551557 : ℝ) := by
  have he : exp (1 : ℝ) < 68 / 25 := by linarith [Real.exp_one_lt_d9]
  have hpow : (exp (1 : ℝ)) ^ 44 < (68 / 25 : ℝ) ^ 44 :=
    pow_lt_pow_left₀ he (exp_pos 1).le (by norm_num)
  have h44 : exp (44 : ℝ) = (exp (1 : ℝ)) ^ 44 := by
    simpa using Real.exp_nat_mul (1 : ℝ) 44
  rw [h44]
  norm_num at hpow ⊢
  linarith

theorem finite_exp24_exp44_bridge
    (hQ : Nat.Prime 18446744073709551557)
    (hgap : ConsecutiveGapBound 18446744073709551557 1550)
    {c x : ℝ} (hc : (4 / 5 : ℝ) ≤ c)
    (hx : exp 24 ≤ x) (hx44 : x < exp 44) :
    ∃ q : ℕ, q.Prime ∧ x < q ∧
      (q : ℝ) < x + c * sqrt x * log x :=
  fixed_gap_one_prime hQ hgap hc hx (hx44.trans exp44_lt_terminal)

#print axioms real_bracketing_primes
#print axioms prime_in_real_interval
#print axioms fixed_gap_one_prime
#print axioms exp44_lt_terminal
#print axioms finite_exp24_exp44_bridge
end RHOnePrime.FiniteGap
