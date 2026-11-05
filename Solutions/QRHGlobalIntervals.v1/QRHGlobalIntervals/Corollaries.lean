/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Powers
import QRHGlobalIntervals.TwentyFourth

/-!
# Oppermann- and Andrica-type statements at exponent `1/8`, under QRH

Oppermann's conjecture asks for primes in `(n² − n, n²)` and `(n², n² + n)`; Andrica's asks for
`√p' − √p < 1` for consecutive primes. Both are far beyond RH. With exponent `7/8` in place of
`1/2` the analogues follow from `global_interval` and `twentyfourth_interval`:

* `oppermann_powers`: for `k ≥ 8` and `n ≥ 2`, primes in `(n^k − n^{k−1}, n^k)` and
  `(n^k, n^k + n^{k−1})`.
* `andrica_eighth`: for consecutive primes `p < p'`, `p'^{1/8} − p^{1/8} ≤ 1/8`;
  `andrica_eighth_24`: `≤ 1/192` once `p ≥ 1339`.

The binomial step is `(a + b)^8 ≥ a^8 + 8a^7b` for `a, b ≥ 0`, at `a = p^{1/8}`.
-/

namespace QRHGlobal

open Real IEANTN

theorem pow_seven_eighths_le {n k : ℕ} (hn : 1 ≤ n) (hk : 8 ≤ k) :
    ((n ^ k : ℕ) : ℝ) ^ ((7 : ℝ) / 8) ≤ ((n ^ (k - 1) : ℕ) : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  rw [← rpow_natCast (n : ℝ) k, ← rpow_mul (by positivity), ← rpow_natCast (n : ℝ) (k - 1)]
  apply rpow_le_rpow_of_exponent_le hn1
  have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hk']
  have : (8 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- **Oppermann-type intervals.** For every `k ≥ 8` and `n ≥ 2` there are primes in
`(n^k − n^{k−1}, n^k)` and in `(n^k, n^k + n^{k−1})`. -/
theorem oppermann_powers (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion)
    {k n : ℕ} (hk : 8 ≤ k) (hn : 2 ≤ n) :
    (∃ p : ℕ, p.Prime ∧ n ^ k - n ^ (k - 1) < p ∧ p < n ^ k) ∧
      (∃ p : ℕ, p.Prime ∧ n ^ k < p ∧ p < n ^ k + n ^ (k - 1)) := by
  have hpowk : n ^ k = n * n ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hsmall : n ^ (k - 1) < n ^ k := by
    rw [hpowk]
    have : 0 < n ^ (k - 1) := pow_pos (by omega) _
    nlinarith
  have hnk1 : 2 ≤ n ^ (k - 1) := by
    calc 2 ≤ n := hn
      _ = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hw := pow_seven_eighths_le (n := n) (k := k) (by omega) hk
  constructor
  · -- left interval: start at y = n^k − n^{k−1}
    set y := n ^ k - n ^ (k - 1) with hy
    have hy1 : 1 ≤ y := by omega
    have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
    obtain ⟨p, hp, hlt, hle⟩ := global_interval hθ hD hcrit (y : ℝ) hyR
    have hyw : (y : ℝ) ^ ((7 : ℝ) / 8) ≤ ((n ^ k : ℕ) : ℝ) ^ ((7 : ℝ) / 8) :=
      rpow_le_rpow (by positivity) (by exact_mod_cast (Nat.sub_le _ _)) (by norm_num)
    have hyk : ((y : ℕ) : ℝ) + ((n ^ (k - 1) : ℕ) : ℝ) = ((n ^ k : ℕ) : ℝ) := by
      rw [hy]; push_cast [Nat.cast_sub hsmall.le]; ring
    have hpk : p ≤ n ^ k := by
      have : (p : ℝ) ≤ ((n ^ k : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hne : p ≠ n ^ k := by
      intro h
      rw [h, hpowk] at hp
      exact Nat.not_prime_mul (by omega) (by omega) hp
    exact ⟨p, hp, by exact_mod_cast hlt, lt_of_le_of_ne hpk hne⟩
  · have hx : (1 : ℝ) ≤ ((n ^ k : ℕ) : ℝ) := by
      have : 1 ≤ n ^ k := Nat.one_le_pow _ _ (by omega)
      exact_mod_cast this
    obtain ⟨p, hp, hlt, hle⟩ := global_interval hθ hD hcrit _ hx
    have hpk : p ≤ n ^ k + n ^ (k - 1) := by
      have : (p : ℝ) ≤ ((n ^ k + n ^ (k - 1) : ℕ) : ℝ) := by push_cast at hw hle ⊢; linarith
      exact_mod_cast this
    have hne : p ≠ n ^ k + n ^ (k - 1) := by
      intro h
      have hf : n ^ k + n ^ (k - 1) = n ^ (k - 1) * (n + 1) := by rw [hpowk]; ring
      rw [h, hf] at hp
      exact Nat.not_prime_mul (by omega) (by omega) hp
    exact ⟨p, hp, by exact_mod_cast hlt, lt_of_le_of_ne hpk hne⟩

/-- `(a + b)^8 ≥ a^8 + 8·a^7·b` for `a, b ≥ 0`. -/
theorem add_pow_eight_ge {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 8 + 8 * a ^ 7 * b ≤ (a + b) ^ 8 := by
  have h : (a + b) ^ 8 - (a ^ 8 + 8 * a ^ 7 * b) =
      b ^ 2 * (28 * a ^ 6 + 56 * a ^ 5 * b + 70 * a ^ 4 * b ^ 2 + 56 * a ^ 3 * b ^ 3 +
        28 * a ^ 2 * b ^ 4 + 8 * a * b ^ 5 + b ^ 6) := by ring
  have : 0 ≤ b ^ 2 * (28 * a ^ 6 + 56 * a ^ 5 * b + 70 * a ^ 4 * b ^ 2 + 56 * a ^ 3 * b ^ 3 +
      28 * a ^ 2 * b ^ 4 + 8 * a * b ^ 5 + b ^ 6) := by positivity
  linarith

/-- If `q ≤ p + c·p^{7/8}` then `q^{1/8} ≤ p^{1/8} + c/8`. -/
theorem eighth_root_step {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (h : q ≤ p + c * p ^ ((7 : ℝ) / 8)) : q ^ ((1 : ℝ) / 8) ≤ p ^ ((1 : ℝ) / 8) + c / 8 := by
  set a := p ^ ((1 : ℝ) / 8) with ha
  have ha0 : 0 ≤ a := rpow_nonneg hp _
  have ha8 : a ^ 8 = p := by
    rw [ha, ← rpow_natCast, ← rpow_mul hp]; norm_num
  have ha7 : a ^ 7 = p ^ ((7 : ℝ) / 8) := by
    rw [ha, ← rpow_natCast, ← rpow_mul hp]; norm_num
  have hbin := add_pow_eight_ge ha0 (show 0 ≤ c / 8 by positivity)
  have hq8 : q ≤ (a + c / 8) ^ 8 := by
    calc q ≤ p + c * p ^ ((7 : ℝ) / 8) := h
      _ = a ^ 8 + 8 * a ^ 7 * (c / 8) := by rw [ha8, ha7]; ring
      _ ≤ _ := hbin
  have hb0 : 0 ≤ a + c / 8 := by positivity
  calc q ^ ((1 : ℝ) / 8) ≤ ((a + c / 8) ^ 8) ^ ((1 : ℝ) / 8) :=
        rpow_le_rpow hq hq8 (by norm_num)
    _ = a + c / 8 := by
        rw [← rpow_natCast, ← rpow_mul hb0]; norm_num

/-- **Andrica-type, exponent `1/8`.** For consecutive primes `p < p'`, `p'^{1/8} − p^{1/8} ≤ 1/8`. -/
theorem andrica_eighth (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion)
    {p p' : ℕ} (hp : p.Prime) (_hlt : p < p') (hnext : ∀ r : ℕ, p < r → r < p' → ¬ r.Prime) :
    (p' : ℝ) ^ ((1 : ℝ) / 8) - (p : ℝ) ^ ((1 : ℝ) / 8) ≤ 1 / 8 := by
  obtain ⟨r, hr, hpr, hle⟩ := prime_gap_le hθ hD hcrit hp
  have hp'r : p' ≤ r := by
    by_contra hcon
    exact hnext r hpr (not_le.mp hcon) hr
  have hq : (p' : ℝ) ≤ p + 1 * (p : ℝ) ^ ((7 : ℝ) / 8) := by
    have : (p' : ℝ) ≤ r := by exact_mod_cast hp'r
    linarith
  have := eighth_root_step (Nat.cast_nonneg p) (Nat.cast_nonneg p') zero_le_one hq
  linarith

/-- **Andrica-type, from `1339`.** For consecutive primes `p < p'` with `p ≥ 1339`,
`p'^{1/8} − p^{1/8} ≤ 1/192`. -/
theorem andrica_eighth_24 (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hKL : KadiriLumley.v1.table_2)
    (hψ : BKLNW.v1.table8_psi_bound_above) (hcor : BKLNW.v1.corollary_5_1_above)
    (hcrit : PrimeInterval.v1.eTheta_criterion)
    {p p' : ℕ} (h1339 : 1339 ≤ p) (_hlt : p < p') (hnext : ∀ r : ℕ, p < r → r < p' → ¬ r.Prime) :
    (p' : ℝ) ^ ((1 : ℝ) / 8) - (p : ℝ) ^ ((1 : ℝ) / 8) ≤ 1 / 192 := by
  obtain ⟨r, hr, hpr, hle⟩ := prime_gap_twentyfourth hθ hD hKL hψ hcor hcrit h1339
  have hp'r : p' ≤ r := by
    by_contra hcon
    exact hnext r hpr (not_le.mp hcon) hr
  have hq : (p' : ℝ) ≤ p + (1 / 24) * (p : ℝ) ^ ((7 : ℝ) / 8) := by
    have : (p' : ℝ) ≤ r := by exact_mod_cast hp'r
    linarith
  have := eighth_root_step (Nat.cast_nonneg p) (Nat.cast_nonneg p') (by norm_num) hq
  linarith

end QRHGlobal
