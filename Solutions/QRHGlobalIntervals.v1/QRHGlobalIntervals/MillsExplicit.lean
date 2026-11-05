/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import QRHGlobalIntervals.Mills
import Mathlib.NumberTheory.LucasPrimality

/-!
# An explicit Mills constant for the exponent 8, under QRH

Least choices from `p₀ = 2`: `p₁ = 257` (the least prime above `2^8`) and
`p₂ = 19031147999601100901 = 257^8 + 100`. Continuing `mills_qrh` from `p₂` and taking a 64th root
gives `A` with `⌊A⌋ = 2`, `⌊A^8⌋ = 257`, `⌊A^64⌋ = p₂` and `⌊A^{8^n}⌋` prime for every `n`, hence

  `2.000974897633077337586 ≤ A < 2.000974897633077337588`,

twenty decimals of the constant (`mills_explicit`). Every later term only refines `A` inside
`[p₂^{1/64}, (p₂ + 1)^{1/64})`.

`p₂` is proved prime by a Lucas certificate (`Mathlib`'s `lucas_primality`) with the factorization
`p₂ − 1 = 2²·5²·222799·854184623791`, itself certified (`854184623791 − 1 = 2·3·5·73·149·1031·2539`).
The modular powers are computed by the kernel through `powMod` (square and multiply, proved equal to
`b^e % m`); no native evaluation.
-/

namespace QRHGlobal

open Real IEANTN

/-! ### Kernel-evaluable modular powers -/

/-- `acc·b^e mod m` by square and multiply, while `e < 2^fuel`. -/
def powModAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc % m
  | fuel + 1, b, e, acc =>
      if e = 0 then acc % m
      else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

theorem powModAux_spec (m : ℕ) : ∀ (fuel b e acc : ℕ), e < 2 ^ fuel →
    powModAux m fuel b e acc = acc * b ^ e % m
  | 0, b, e, acc, h => by
      have he : e = 0 := by simpa using h
      subst he
      simp [powModAux]
  | fuel + 1, b, e, acc, h => by
      have h2 : e / 2 < 2 ^ fuel := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        rw [pow_succ] at h
        exact h
      by_cases he : e = 0
      · subst he
        simp [powModAux]
      have hsplit := Nat.div_add_mod e 2
      simp only [powModAux, he, ite_false]
      rw [powModAux_spec m fuel _ _ _ h2]
      by_cases hodd : e % 2 = 1
      · simp only [hodd, ite_true]
        have hm : acc * b % m * (b * b % m) ^ (e / 2) ≡ acc * b * (b * b) ^ (e / 2) [MOD m] :=
          Nat.ModEq.mul (Nat.mod_modEq _ _) (Nat.ModEq.pow _ (Nat.mod_modEq _ _))
        have hpow : acc * b * (b * b) ^ (e / 2) = acc * b ^ e := by
          conv_rhs => rw [← hsplit, hodd]
          rw [pow_add, pow_mul, pow_one, ← sq]
          ring
        rw [hpow] at hm
        exact hm
      · have hev : e % 2 = 0 := by omega
        simp only [hodd, ite_false]
        have hm : acc * (b * b % m) ^ (e / 2) ≡ acc * (b * b) ^ (e / 2) [MOD m] :=
          Nat.ModEq.mul_left _ (Nat.ModEq.pow _ (Nat.mod_modEq _ _))
        have hpow : acc * (b * b) ^ (e / 2) = acc * b ^ e := by
          conv_rhs => rw [← hsplit, hev]
          rw [add_zero, pow_mul, ← sq]
        rw [hpow] at hm
        exact hm

/-- Modular power, exact for exponents below `2^70`. -/
def powMod (b e m : ℕ) : ℕ := powModAux m 70 (b % m) e 1

theorem powMod_eq {b e m : ℕ} (he : e < 2 ^ 70) : powMod b e m = b ^ e % m := by
  rw [powMod, powModAux_spec m 70 _ _ _ he, one_mul]
  exact (Nat.pow_mod b e m).symm

theorem mem_of_prime_dvd_prod {q : ℕ} (hq : q.Prime) :
    ∀ ps : List ℕ, (∀ r ∈ ps, r.Prime) → q ∣ ps.prod → q ∈ ps
  | [], _, h => by
      simp only [List.prod_nil, Nat.dvd_one] at h
      exact absurd h hq.one_lt.ne'
  | r :: rs, hps, h => by
      rw [List.prod_cons] at h
      rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
      · have := (Nat.prime_dvd_prime_iff_eq hq (hps r (by simp))).mp h1
        simp [this]
      · exact List.mem_cons_of_mem _
          (mem_of_prime_dvd_prod hq rs (fun t ht => hps t (by simp [ht])) h1)

/-- **Lucas, with a factored `p − 1` and kernel-computed powers.** -/
theorem prime_of_lucas {p a : ℕ} (ps : List ℕ) (hp : 1 < p) (hprod : ps.prod = p - 1)
    (hps : ∀ r ∈ ps, r.Prime) (hsmall : p - 1 < 2 ^ 70) (ha : powMod a (p - 1) p = 1)
    (hq : ∀ q ∈ ps, powMod a ((p - 1) / q) p ≠ 1) : p.Prime := by
  have hcast : ∀ e : ℕ, e < 2 ^ 70 → ((a : ZMod p) ^ e = 1 ↔ powMod a e p = 1) := by
    intro e he
    rw [← Nat.cast_pow, ← ZMod.natCast_mod, ← powMod_eq he, ← Nat.cast_one,
      ZMod.natCast_eq_natCast_iff']
    have hlt : powMod a e p < p := by rw [powMod_eq he]; exact Nat.mod_lt _ (by omega)
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hp]
  apply lucas_primality p (a : ZMod p)
  · exact (hcast _ hsmall).mpr ha
  · intro q hqp hdvd
    have hmem := mem_of_prime_dvd_prod hqp ps hps (hprod ▸ hdvd)
    have he : (p - 1) / q < 2 ^ 70 := lt_of_le_of_lt (Nat.div_le_self _ _) hsmall
    intro h1
    exact hq q hmem ((hcast _ he).mp h1)

set_option maxRecDepth 100000 in
theorem prime_854184623791 : Nat.Prime 854184623791 :=
  prime_of_lucas (a := 7) [2, 3, 5, 73, 149, 1031, 2539] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons]; norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- The third term of the least Mills sequence for the exponent 8. -/
theorem prime_p2 : Nat.Prime 19031147999601100901 :=
  prime_of_lucas (a := 2) [2, 2, 5, 5, 222799, 854184623791] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons]; exact ⟨Nat.prime_two, Nat.prime_two, by norm_num,
      by norm_num, by norm_num, prime_854184623791, by simp⟩) (by norm_num) (by decide +kernel)
    (by decide +kernel)

/-- `p₂ = 257^8 + 100`, so `p₂ ∈ (257^8, 258^8)`. -/
theorem p2_eq : (19031147999601100901 : ℕ) = 257 ^ 8 + 100 := by norm_num

/-- **An explicit Mills constant, under QRH.** -/
theorem mills_explicit (hθ : QRHPropagation.v2.theta_frontier)
    (hD : Dusart2018.v1.proposition_5_4) (hcrit : PrimeInterval.v1.eTheta_criterion) :
    ∃ A : ℝ, (∀ n : ℕ, (⌊A ^ (8 ^ n : ℕ)⌋₊).Prime) ∧ ⌊A⌋₊ = 2 ∧ ⌊A ^ 8⌋₊ = 257 ∧
      ⌊A ^ 64⌋₊ = 19031147999601100901 ∧
      (2.000974897633077337586 : ℝ) ≤ A ∧ A < 2.000974897633077337588 := by
  obtain ⟨B, hB1, hB2, hB3⟩ := mills_qrh hθ hD hcrit (k := 8) le_rfl prime_p2
  have hB0 : 0 ≤ B := le_trans (by positivity) hB1
  set A := B ^ ((1 : ℝ) / 64) with hA
  have hA0 : 0 ≤ A := rpow_nonneg hB0 _
  have hpowA : ∀ j : ℕ, A ^ (64 * j) = B ^ j := by
    intro j
    rw [pow_mul, hA, ← rpow_natCast (B ^ ((1 : ℝ) / 64)) 64, ← rpow_mul hB0]
    norm_num
  have hA64 : A ^ 64 = B := by simpa using hpowA 1
  -- B ∈ [p₂, p₂ + 1)
  have hB1' : (19031147999601100901 : ℝ) ≤ B := by exact_mod_cast hB1
  have hB2' : B < 19031147999601100902 := by
    have := hB2
    norm_num at this
    linarith
  -- the floors at levels 0, 1, 2
  have hfloorB : ⌊A ^ 64⌋₊ = 19031147999601100901 := by
    rw [hA64, Nat.floor_eq_iff hB0]
    exact ⟨by exact_mod_cast hB1', by push_cast; linarith⟩
  have hA8 : (A ^ 8) ^ 8 = B := by rw [← pow_mul]; exact hA64
  have hfloor8 : ⌊A ^ 8⌋₊ = 257 := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor
    · by_contra hc
      push Not at hc
      have : (A ^ 8) ^ 8 < (257 : ℝ) ^ 8 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
      rw [hA8] at this
      linarith
    · by_contra hc
      push Not at hc
      have : (258 : ℝ) ^ 8 ≤ (A ^ 8) ^ 8 := pow_le_pow_left₀ (by norm_num) (by push_cast at hc; linarith) 8
      rw [hA8] at this
      linarith
  have hfloor1 : ⌊A⌋₊ = 2 := by
    rw [Nat.floor_eq_iff hA0]
    constructor
    · by_contra hc
      push Not at hc
      have : A ^ 64 < (2 : ℝ) ^ 64 := pow_lt_pow_left₀ hc hA0 (by norm_num)
      rw [hA64] at this
      norm_num at this
      linarith
    · by_contra hc
      push Not at hc
      have : (3 : ℝ) ^ 64 ≤ A ^ 64 := pow_le_pow_left₀ (by norm_num) (by push_cast at hc; linarith) 64
      rw [hA64] at this
      norm_num at this
      linarith
  refine ⟨A, ?_, hfloor1, hfloor8, hfloorB, ?_, ?_⟩
  · intro n
    match n with
    | 0 => simp only [pow_zero, pow_one]; rw [hfloor1]; exact Nat.prime_two
    | 1 => simp only [pow_one]; rw [hfloor8]; norm_num
    | n + 2 =>
      have h := hB3 n
      have e : A ^ (8 ^ (n + 2) : ℕ) = B ^ ((8 : ℝ) ^ n) := by
        rw [show (8 ^ (n + 2) : ℕ) = 64 * 8 ^ n by ring, hpowA, ← rpow_natCast]
        push_cast; rfl
      rw [e]; exact h
  · by_contra hc
    push Not at hc
    have : A ^ 64 < (2.000974897633077337586 : ℝ) ^ 64 := pow_lt_pow_left₀ hc hA0 (by norm_num)
    rw [hA64] at this
    have hn : (19031147999601100901 : ℝ) ≥ (2.000974897633077337586 : ℝ) ^ 64 := by norm_num
    linarith
  · by_contra hc
    push Not at hc
    have : (2.000974897633077337588 : ℝ) ^ 64 ≤ A ^ 64 := pow_le_pow_left₀ (by norm_num) hc 64
    rw [hA64] at this
    have hn : (19031147999601100902 : ℝ) ≤ (2.000974897633077337588 : ℝ) ^ 64 := by norm_num
    linarith

end QRHGlobal

