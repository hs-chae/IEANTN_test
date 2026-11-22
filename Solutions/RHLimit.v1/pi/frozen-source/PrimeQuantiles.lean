/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import QuarticWindow

/-! The same actual prime-count interface now controls whole blocks of consecutive primes.
`Nat.nth Nat.Prime` is indexed from zero: index zero is the prime two.
No analytic prime-distribution hypothesis is hidden in this discrete adapter. -/
namespace RHContinuation.PrimeQuantiles
open Real Nat

theorem count_at_nth (n : ℕ) :
    Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_succ]
  simp only [Nat.prime_nth_prime, if_true]
  change Nat.primeCounting' (Nat.nth Nat.Prime n) + 1 = n + 1
  rw [Nat.primeCounting'_nth_eq]

/-- A count lower bound gives an actual contiguous block of prime-index quantiles. -/
theorem quantile_from_count {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    {m : ℕ} (hcount : (m : ℝ) <
      QuarticWindow.primeCounting y - QuarticWindow.primeCounting x) :
    x < (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊x⌋₊ + m) : ℝ) ≤ y := by
  let i := Nat.primeCounting ⌊x⌋₊ + m
  have hnat : i < Nat.primeCounting ⌊y⌋₊ := by
    dsimp [i]
    unfold QuarticWindow.primeCounting at hcount
    have h : (Nat.primeCounting ⌊x⌋₊ : ℝ) + m < Nat.primeCounting ⌊y⌋₊ := by
      linarith
    exact_mod_cast h
  have htop : Nat.nth Nat.Prime i < ⌊y⌋₊ + 1 :=
    Nat.nth_lt_of_lt_count hnat
  have hupper : (Nat.nth Nat.Prime i : ℝ) ≤ y := by
    have hi : Nat.nth Nat.Prime i ≤ ⌊y⌋₊ := by omega
    exact (by exact_mod_cast hi : (Nat.nth Nat.Prime i : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans
      (Nat.floor_le (hx.trans hxy))
  have hlower : x < (Nat.nth Nat.Prime i : ℝ) := by
    by_contra h
    have hinat : Nat.nth Nat.Prime i ≤ ⌊x⌋₊ :=
      Nat.le_floor (le_of_not_gt h)
    have hc := Nat.monotone_primeCounting hinat
    rw [count_at_nth] at hc
    dsimp [i] at hc
    omega
  exact ⟨hlower, hupper⟩

/-- Instantiate every integer count target below the actual new quartic lower count.
The input is a reusable theorem at the actual observable, not an abstract success flag. -/
theorem quartic_quantiles
    (hinterval : ∀ u : ℝ, Real.exp 24 ≤ u →
      (503 / 500 + (26 / 5) / Real.log u) * Real.sqrt u <
        QuarticWindow.primeCounting (u + (111 / 50) * Real.sqrt u * Real.log u) -
          QuarticWindow.primeCounting u)
    {u : ℝ} (hu : Real.exp 24 ≤ u) {m : ℕ}
    (hm : (m : ℝ) ≤ (503 / 500 + (26 / 5) / Real.log u) * Real.sqrt u) :
    u < (Nat.nth Nat.Prime (Nat.primeCounting ⌊u⌋₊ + m) : ℝ) ∧
      (Nat.nth Nat.Prime (Nat.primeCounting ⌊u⌋₊ + m) : ℝ) ≤
        u + (111 / 50) * Real.sqrt u * Real.log u := by
  have hup : 0 < u := (Real.exp_pos _).trans_le hu
  have hul : 0 ≤ Real.log u := Real.log_nonneg (by
    have h := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 24)
    exact h.trans hu)
  apply quantile_from_count hup.le
    (by nlinarith [Real.sqrt_nonneg u])
  exact hm.trans_lt (hinterval u hu)

#print axioms quartic_quantiles
end RHContinuation.PrimeQuantiles
