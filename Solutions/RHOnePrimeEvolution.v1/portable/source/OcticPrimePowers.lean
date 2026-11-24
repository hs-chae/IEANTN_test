/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticTrivial
import Mathlib.NumberTheory.Harmonic.Bounds

namespace RHLimit.OcticPrimePowers
open Real Finset
set_option maxHeartbeats 2000000

noncomputable def gateWeight (n : ℕ) (C L : ℝ) (m : ℕ) : ℝ :=
  if EvenKernel.a C L < (m : ℝ) ∧ (m : ℝ) < EvenKernel.b C L then
    EvenKernel.kernel n ((log (m : ℝ) - L) / EvenKernel.δ C L) *
      ((ArithmeticFunction.vonMangoldt m : ℝ) / sqrt (m : ℝ)) else 0

noncomputable def rootPrimes (a b : ℝ) (k : ℕ) : Finset ℕ :=
  ((Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime).filter
    (fun p => a < ((p ^ k : ℕ) : ℝ) ∧ ((p ^ k : ℕ) : ℝ) < b)

theorem gateWeight_zero (n : ℕ) (C L : ℝ) : gateWeight n C L 0 = 0 := by
  simp [gateWeight]

theorem gateWeight_non_primepow (n : ℕ) (C L : ℝ) {m : ℕ} (hm : ¬ IsPrimePow m) :
    gateWeight n C L m = 0 := by
  simp [gateWeight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm]

theorem mangoldt_eq_primepower_sum (n : ℕ) (C L : ℝ) :
    EvenKernel.mangoldtPopulation n C L =
      ∑ m ∈ Ioc 0 ⌊EvenKernel.b C L⌋₊ with IsPrimePow m, gateWeight n C L m := by
  unfold EvenKernel.mangoldtPopulation
  rw [sum_filter, Nat.range_succ_eq_Icc_zero]
  change (∑ m ∈ Icc 0 ⌊EvenKernel.b C L⌋₊, gateWeight n C L m) = _
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : (0 : ℕ) ≤ ⌊EvenKernel.b C L⌋₊)]
  rw [gateWeight_zero, zero_add, sum_filter]
  apply sum_congr rfl
  intro m hm
  split_ifs with hp
  · rfl
  · exact gateWeight_non_primepow n C L hp

theorem mangoldt_eq_exponent_sum (n : ℕ) (C L : ℝ) :
    EvenKernel.mangoldtPopulation n C L =
      ∑ k ∈ Icc 1 ⌊log (EvenKernel.b C L) / log 2⌋₊,
        ∑ p ∈ Ioc 0 ⌊(EvenKernel.b C L) ^ (1 / (k : ℝ))⌋₊ with p.Prime,
          gateWeight n C L (p ^ k) := by
  rw [mangoldt_eq_primepower_sum, Chebyshev.sum_PrimePow_eq_sum_sum]
  unfold EvenKernel.b
  positivity

theorem exponent_one_population (n : ℕ) (C L : ℝ) :
    (∑ p ∈ Ioc 0 ⌊EvenKernel.b C L⌋₊ with p.Prime,
      gateWeight n C L (p ^ 1)) = EvenKernel.population n C L := by
  have hs : (Ioc 0 ⌊EvenKernel.b C L⌋₊).filter Nat.Prime =
      Nat.primesLE ⌊EvenKernel.b C L⌋₊ := by
    rw [Nat.primesLE_eq_filter_Icc_zero]
    ext p
    simp only [mem_filter, mem_Ioc, mem_Icc, Nat.zero_le, true_and]
    have hp := Nat.Prime.pos (p := p)
    aesop
  rw [hs]
  unfold EvenKernel.population QuarticWindow.primesBetween
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  simp only [pow_one, gateWeight, ArithmeticFunction.vonMangoldt_apply_prime hprime]

theorem rootPrimes_card {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {k : ℕ} (hk : 2 ≤ k) :
    ((rootPrimes a b k).card : ℝ) ≤ b ^ (1 / (k : ℝ)) - a ^ (1 / (k : ℝ)) + 1 := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hroot : a ^ (1 / (k : ℝ)) ≤ b ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow ha.le hab (by positivity)
  have hfloor : ⌊a ^ (1 / (k : ℝ))⌋₊ ≤ ⌊b ^ (1 / (k : ℝ))⌋₊ :=
    Nat.floor_le_floor hroot
  have hsub : rootPrimes a b k ⊆
      Ioc ⌊a ^ (1 / (k : ℝ))⌋₊ ⌊b ^ (1 / (k : ℝ))⌋₊ := by
    intro p hp
    have hgate := (mem_filter.mp hp).2
    have hpdom := (mem_filter.mp (mem_filter.mp hp).1).1
    have hpl : a ^ (1 / (k : ℝ)) < (p : ℝ) := by
      rw [one_div, Real.rpow_inv_lt_iff_of_pos ha.le (Nat.cast_nonneg p) hk0]
      simpa only [Real.rpow_natCast, Nat.cast_pow] using hgate.1
    have hlf := Nat.floor_le (Real.rpow_nonneg ha.le (1 / (k : ℝ)))
    have hpn : ⌊a ^ (1 / (k : ℝ))⌋₊ < p := by exact_mod_cast hlf.trans_lt hpl
    exact mem_Ioc.mpr ⟨hpn, (mem_Ioc.mp hpdom).2⟩
  have hc := Finset.card_le_card hsub
  have hreal : ((rootPrimes a b k).card : ℝ) ≤
      (⌊b ^ (1 / (k : ℝ))⌋₊ : ℝ) - ⌊a ^ (1 / (k : ℝ))⌋₊ := by
    rw [Nat.card_Ioc] at hc
    have h := (Nat.cast_le (α := ℝ)).mpr hc
    rwa [Nat.cast_sub hfloor] at h
  have hbu := Nat.floor_le (Real.rpow_nonneg (ha.le.trans hab) (1 / (k : ℝ)))
  have hal := Nat.lt_floor_add_one (a ^ (1 / (k : ℝ)))
  linarith

theorem exponent_weighted_bound (n : ℕ) {C L : ℝ}
    (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16) (hL : 24 ≤ L) {k : ℕ} (hk : 2 ≤ k) :
    (∑ p ∈ Ioc 0 ⌊(EvenKernel.b C L) ^ (1 / (k : ℝ))⌋₊ with p.Prime,
      gateWeight n C L (p ^ k)) ≤
        (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) / (k : ℝ) *
          ((rootPrimes (EvenKernel.a C L) (EvenKernel.b C L) k).card : ℝ) := by
  let P := (Ioc 0 ⌊(EvenKernel.b C L) ^ (1 / (k : ℝ))⌋₊).filter Nat.Prime
  let w : ℕ → ℝ := fun p => EvenKernel.kernel n
    ((log ((p ^ k : ℕ) : ℝ) - L) / EvenKernel.δ C L) *
      ((ArithmeticFunction.vonMangoldt (p ^ k) : ℝ) / sqrt ((p ^ k : ℕ) : ℝ))
  have heq : (∑ p ∈ P, gateWeight n C L (p ^ k)) =
      ∑ p ∈ rootPrimes (EvenKernel.a C L) (EvenKernel.b C L) k, w p := by
    symm
    unfold rootPrimes
    rw [sum_filter]
    rfl
  change (∑ p ∈ P, gateWeight n C L (p ^ k)) ≤ _
  rw [heq]
  have ha : 0 < EvenKernel.a C L := exp_pos _
  have hsa : 0 < sqrt (EvenKernel.a C L) := Real.sqrt_pos.mpr ha
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  calc
    _ ≤ ∑ _p ∈ rootPrimes (EvenKernel.a C L) (EvenKernel.b C L) k,
        (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) / (k : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hgate := (mem_filter.mp hp).2
      have hprime := (mem_filter.mp (mem_filter.mp hp).1).2
      have hpk : 0 < ((p ^ k : ℕ) : ℝ) := ha.trans hgate.1
      have hs : 0 < sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_pos.mpr hpk
      have hlp : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hprime.one_le)
      have hl := Real.log_le_log hpk hgate.2.le
      rw [Nat.cast_pow, Real.log_pow] at hl
      have hlb : log (p : ℝ) ≤ log (EvenKernel.b C L) / (k : ℝ) :=
        (le_div_iff₀ hkR).mpr (by nlinarith)
      have hroot := Real.sqrt_le_sqrt hgate.1.le
      dsimp [w]
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hprime]
      calc
        _ ≤ log (p : ℝ) / sqrt ((p ^ k : ℕ) : ℝ) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (EvenKernel.kernel_le_one n _) (div_nonneg hlp hs.le)
        _ ≤ log (p : ℝ) / sqrt (EvenKernel.a C L) :=
          div_le_div_of_nonneg_left hlp hsa hroot
        _ ≤ (log (EvenKernel.b C L) / (k : ℝ)) / sqrt (EvenKernel.a C L) :=
          div_le_div_of_nonneg_right hlb hsa.le
        _ = _ := by ring
    _ = _ := by simp [sum_const, nsmul_eq_mul, mul_comm]

theorem exp_sub_le (u v : ℝ) : exp u - exp v ≤ (u - v) * exp u := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (v - u)) (exp_nonneg u)
  have heq : exp u * exp (v - u) = exp v := by rw [← Real.exp_add]; congr 1; ring
  rw [heq] at h
  nlinarith

theorem root_span_bound {C L : ℝ} (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16)
    (hL : 24 ≤ L) {k : ℕ} (hk : 2 ≤ k) :
    (EvenKernel.b C L) ^ (1 / (k : ℝ)) - (EvenKernel.a C L) ^ (1 / (k : ℝ)) ≤
      (2 * EvenKernel.δ C L / (k : ℝ)) * sqrt (EvenKernel.b C L) := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hd := RHLimit.OcticGeometry.delta_nonneg hC.1 hL
  have hpos : 0 ≤ L + EvenKernel.δ C L := by linarith
  have hre : ∀ x : ℝ, (exp x) ^ (1 / (k : ℝ)) = exp (x / (k : ℝ)) := by
    intro x
    rw [Real.rpow_def_of_pos (exp_pos _), Real.log_exp]
    congr 1
    ring
  unfold EvenKernel.a EvenKernel.b
  rw [hre, hre]
  have h := exp_sub_le ((L + EvenKernel.δ C L) / (k : ℝ))
    ((L - EvenKernel.δ C L) / (k : ℝ))
  have heq : (L + EvenKernel.δ C L) / (k : ℝ) -
      (L - EvenKernel.δ C L) / (k : ℝ) = 2 * EvenKernel.δ C L / (k : ℝ) := by ring
  rw [heq] at h
  calc
    _ ≤ (2 * EvenKernel.δ C L / (k : ℝ)) * exp ((L + EvenKernel.δ C L) / (k : ℝ)) := h
    _ ≤ (2 * EvenKernel.δ C L / (k : ℝ)) * exp ((L + EvenKernel.δ C L) / 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_left hpos (by norm_num) hk2
    _ = _ := by rw [Real.exp_half]

theorem reciprocal_tail_le_log {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Icc 2 K, 1 / (k : ℝ)) ≤ log (K : ℝ) := by
  have h := harmonic_le_one_add_log K
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
  rw [← Finset.sum_erase_add (Icc 1 K) _ (left_mem_Icc.mpr hK)] at h
  have heq : (Icc 1 K).erase 1 = Icc 2 K := by ext k; simp; omega
  rw [heq] at h
  norm_num at h
  simpa only [one_div] using (show (∑ k ∈ Icc 2 K, (k : ℝ)⁻¹) ≤ log (K : ℝ) by linarith)

theorem reciprocal_square_tail_le {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Icc 2 K, 1 / (k : ℝ) ^ 2) ≤ 1 - 1 / (K : ℝ) := by
  induction K with
  | zero => omega
  | succ j ih =>
      by_cases hj : j = 0
      · subst j
        norm_num
      have hj1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj
      have hprev := ih hj1
      change (∑ k ∈ Icc 2 (j + 1), 1 / (k : ℝ) ^ 2) ≤ 1 - 1 / ((j + 1 : ℕ) : ℝ)
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ j + 1)]
      have hjR : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
      have heq : 1 / (j : ℝ) - 1 / ((j : ℝ) + 1) =
          1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
        field_simp [hjR.ne', (show (j : ℝ) + 1 ≠ 0 by positivity)] <;> ring
      have hfrac : 1 / ((j : ℝ) + 1) ^ 2 ≤
          1 / (j : ℝ) - 1 / ((j : ℝ) + 1) := by
        rw [heq]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have hfracNat : 1 / ((j + 1 : ℕ) : ℝ) ^ 2 ≤
          1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hfrac
      calc
        _ ≤ (1 - 1 / (j : ℝ)) + (1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ)) :=
          add_le_add hprev hfracNat
        _ = _ := by ring

theorem primepower_cost_envelope (n : ℕ) {C L : ℝ}
    (hC : C ∈ Set.Icc (103 / 100 : ℝ) 16) (hL : 24 ≤ L) :
    EvenKernel.mangoldtPopulation n C L - EvenKernel.population n C L ≤
      (log (EvenKernel.b C L) / sqrt (EvenKernel.a C L)) *
        (2 * EvenKernel.δ C L * sqrt (EvenKernel.b C L) +
          log (⌊log (EvenKernel.b C L) / log 2⌋₊ : ℝ)) := by
  let a := EvenKernel.a C L
  let b := EvenKernel.b C L
  let K := ⌊log b / log 2⌋₊
  let pref := log b / sqrt a
  let S : ℕ → ℝ := fun k => ∑ p ∈ Ioc 0 ⌊b ^ (1 / (k : ℝ))⌋₊ with p.Prime,
    gateWeight n C L (p ^ k)
  have hd := RHLimit.OcticGeometry.delta_nonneg hC.1 hL
  have ha : 0 < a := exp_pos _
  have hab : a ≤ b := by
    dsimp [a, b, EvenKernel.a, EvenKernel.b]
    apply Real.exp_le_exp.mpr
    linarith
  have hlb : log b = L + EvenKernel.δ C L := Real.log_exp _
  have hlogb : 0 < log b := by rw [hlb]; linarith
  have hpref : 0 ≤ pref := div_nonneg hlogb.le (sqrt_nonneg _)
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlog2u : log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hK : 1 ≤ K := by
    apply (Nat.one_le_floor_iff _).mpr
    apply (one_le_div hlog2).mpr
    rw [hlb]
    linarith
  have hterm : ∀ k ∈ Icc 2 K, S k ≤
      pref * (2 * EvenKernel.δ C L * sqrt b / (k : ℝ) ^ 2 + 1 / (k : ℝ)) := by
    intro k hk
    have hk2 := (mem_Icc.mp hk).1
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hc := rootPrimes_card ha hab hk2
    have hr := root_span_bound hC hL hk2
    have hw := exponent_weighted_bound n hC hL hk2
    change S k ≤ (pref / (k : ℝ)) *
      ((rootPrimes a b k).card : ℝ) at hw
    calc
      S k ≤ (pref / (k : ℝ)) * ((rootPrimes a b k).card : ℝ) := hw
      _ ≤ (pref / (k : ℝ)) * (b ^ (1 / (k : ℝ)) - a ^ (1 / (k : ℝ)) + 1) :=
        mul_le_mul_of_nonneg_left hc (div_nonneg hpref hkR.le)
      _ ≤ (pref / (k : ℝ)) * ((2 * EvenKernel.δ C L / (k : ℝ)) * sqrt b + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hpref hkR.le)
      _ = _ := by field_simp [hkR.ne'] <;> ring
  have hsquare : (∑ k ∈ Icc 2 K, 1 / (k : ℝ) ^ 2) ≤ 1 := by
    have hh := reciprocal_square_tail_le hK
    have hz : 0 ≤ 1 / (K : ℝ) := by positivity
    linarith
  have hharm := reciprocal_tail_le_log hK
  have hsum : (∑ k ∈ Icc 2 K, S k) ≤
      pref * (2 * EvenKernel.δ C L * sqrt b + log (K : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Icc 2 K,
          pref * (2 * EvenKernel.δ C L * sqrt b / (k : ℝ) ^ 2 + 1 / (k : ℝ)) :=
        sum_le_sum hterm
      _ = pref * (2 * EvenKernel.δ C L * sqrt b *
          (∑ k ∈ Icc 2 K, 1 / (k : ℝ) ^ 2) + (∑ k ∈ Icc 2 K, 1 / (k : ℝ))) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
          div_eq_mul_inv, one_mul, mul_assoc]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hpref
        have hm := mul_le_mul_of_nonneg_left hsquare
          (show 0 ≤ 2 * EvenKernel.δ C L * sqrt b by positivity)
        linarith
  have hsplit : (∑ k ∈ Icc 1 K, S k) = S 1 + ∑ k ∈ Icc 2 K, S k := by
    rw [← Finset.sum_erase_add (Icc 1 K) S (left_mem_Icc.mpr hK)]
    have heq : (Icc 1 K).erase 1 = Icc 2 K := by ext k; simp; omega
    rw [heq]
    ring
  have hs1 : S 1 = EvenKernel.population n C L := by
    dsimp [S]
    norm_num only [Nat.cast_one, div_one, Real.rpow_one]
    exact exponent_one_population n C L
  have hM : EvenKernel.mangoldtPopulation n C L =
      EvenKernel.population n C L + ∑ k ∈ Icc 2 K, S k := by
    rw [mangoldt_eq_exponent_sum]
    change (∑ k ∈ Icc 1 K, S k) = _
    rw [hsplit, hs1]
  change _ ≤ pref * (2 * EvenKernel.δ C L * sqrt b + log (K : ℝ))
  linarith

#print axioms mangoldt_eq_exponent_sum
#print axioms rootPrimes_card
#print axioms exponent_weighted_bound
#print axioms root_span_bound
#print axioms reciprocal_tail_le_log
#print axioms reciprocal_square_tail_le
end RHLimit.OcticPrimePowers
