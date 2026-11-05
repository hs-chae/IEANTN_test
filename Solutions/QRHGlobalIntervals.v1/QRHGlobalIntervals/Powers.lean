/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Global

/-!
# A prime between consecutive `k`-th powers, `k ≥ 8`

At `x = n^k`, `x^{7/8} = n^{7k/8} ≤ n^{k-1}` once `k ≥ 8`, and `(n+1)^k ≥ n^k + n^{k-1} + 1`, so the
prime of `global_interval` in `(n^k, n^k + n^{7k/8}]` lies strictly between `n^k` and `(n+1)^k`.
The exponent `8 = 1/(1 - 7/8)` is where the method stops: for `k = 7` the gap `≈ 7x^{6/7}` is
eventually shorter than `x^{7/8}`.
-/

namespace QRHGlobal

open Real IEANTN

theorem succ_pow_gt (n k : ℕ) (hk : 2 ≤ k) : n ^ k + n ^ (k - 1) < (n + 1) ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h1 : n ^ (j + 1) < (n + 1) ^ (j + 1) := by
    exact Nat.pow_lt_pow_left (Nat.lt_succ_self n) (by omega)
  have h2 : n * n ^ (j + 1) ≤ n * (n + 1) ^ (j + 1) :=
    Nat.mul_le_mul_left n h1.le
  calc n ^ (j + 2) + n ^ (j + 2 - 1) = n * n ^ (j + 1) + n ^ (j + 1) := by
        rw [show j + 2 - 1 = j + 1 by omega, pow_succ]; ring
    _ < n * (n + 1) ^ (j + 1) + (n + 1) ^ (j + 1) := by omega
    _ = (n + 1) ^ (j + 2) := by ring

/-- **Consecutive powers.** Under the same inputs, for every `k ≥ 8` and `n ≥ 1` there is a prime
strictly between `n^k` and `(n+1)^k`. -/
theorem prime_between_powers (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion)
    {k n : ℕ} (hk : 8 ≤ k) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n ^ k < p ∧ p < (n + 1) ^ k := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx : (1 : ℝ) ≤ ((n ^ k : ℕ) : ℝ) := by
    push_cast; exact one_le_pow₀ hn1
  obtain ⟨p, hp, hlt, hle⟩ := global_interval hθ hD hcrit _ hx
  refine ⟨p, hp, by exact_mod_cast hlt, ?_⟩
  have hpow : ((n ^ k : ℕ) : ℝ) ^ ((7 : ℝ) / 8) ≤ ((n ^ (k - 1) : ℕ) : ℝ) := by
    push_cast
    rw [← rpow_natCast (n : ℝ) k, ← rpow_mul (by positivity), ← rpow_natCast (n : ℝ) (k - 1)]
    apply rpow_le_rpow_of_exponent_le hn1
    have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; norm_num
    rw [hk']
    have : (8 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hgap := succ_pow_gt n k (by omega)
  have hR : (p : ℝ) < (((n + 1) ^ k : ℕ) : ℝ) := by
    have : (((n ^ k + n ^ (k - 1) : ℕ)) : ℝ) < (((n + 1) ^ k : ℕ) : ℝ) := by exact_mod_cast hgap
    push_cast at this hpow hle ⊢
    linarith
  exact_mod_cast hR

end QRHGlobal
