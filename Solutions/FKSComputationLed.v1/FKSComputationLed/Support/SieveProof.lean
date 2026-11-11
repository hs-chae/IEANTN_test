/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import Mathlib
import FKSComputationLed.Support.SieveRuntime
namespace FKSComputationLed.Sieve

theorem trialLoop_correct (n next fuel : Nat) :
    trialLoop n next fuel = true ↔ ∀ t < fuel, n % (next+t) ≠ 0 := by
  induction fuel generalizing next with
  | zero => simp [trialLoop]
  | succ fuel ih =>
    simp only [trialLoop]
    split_ifs with hzero
    · simp only [Bool.false_eq_true, false_iff]
      intro h
      exact h 0 (by omega) (by simpa using hzero)
    · rw [ih]
      constructor
      · intro h t ht
        cases t with
        | zero => simpa using hzero
        | succ t =>
          have hi : next+(t+1) = next+1+t := by omega
          simpa only [hi] using h t (by omega)
      · intro h t ht
        have hi : next+1+t = next+(t+1) := by omega
        simpa only [hi] using h (t+1) (by omega)

theorem basePrime_correct (n : Nat) : basePrime n = true ↔ Nat.Prime n := by
  unfold basePrime
  split_ifs with hsmall
  · simp only [Bool.false_eq_true, false_iff]
    intro hp
    have := hp.two_le
    omega
  · rw [trialLoop_correct, Nat.prime_def_le_sqrt]
    constructor
    · intro h
      refine ⟨by omega, ?_⟩
      intro m hm hs hd
      have ht : m-2 < Nat.sqrt n+1-2 := by omega
      have hz := h (m-2) ht
      exact hz (by simpa [Nat.add_sub_of_le hm] using Nat.mod_eq_zero_of_dvd hd)
    · rintro ⟨hn, h⟩ t ht hz
      have h2 : 2 ≤ 2+t := by omega
      have hs : 2+t ≤ Nat.sqrt n := by omega
      exact h (2+t) h2 hs (Nat.dvd_of_mod_eq_zero hz)

theorem markLoop_size (p next fuel : Nat) (a : Array Bool) :
    (markLoop p next fuel a).size = a.size := by
  induction fuel generalizing next a with
  | zero => rfl
  | succ fuel ih => simp [markLoop, ih]

theorem sieveRead_set_false {a : Array Bool} {n i : Nat} (hn : n < a.size) :
    sieveRead (a.setIfInBounds i false) n = false ↔ sieveRead a n = false ∨ n = i := by
  simp only [sieveRead, Array.getElem?_setIfInBounds]
  by_cases hi : i = n
  · subst i
    simp [hn]
  · simp [hi, Ne.symm hi]

theorem markLoop_false (p next fuel : Nat) (a : Array Bool) {n : Nat} (hn : n < a.size) :
    sieveRead (markLoop p next fuel a) n = false ↔
      sieveRead a n = false ∨ ∃ t < fuel, n = p*(next+t) := by
  induction fuel generalizing next a with
  | zero => simp [markLoop]
  | succ fuel ih =>
    rw [markLoop, ih (next+1) (a.setIfInBounds (p*next) false) (by simpa using hn), sieveRead_set_false hn]
    constructor
    · rintro ((h | h) | ⟨t, ht, he⟩)
      · exact Or.inl h
      · exact Or.inr ⟨0, by omega, by simpa using h⟩
      · refine Or.inr ⟨t+1, by omega, ?_⟩
        convert he using 1 <;> ring
    · rintro (h | ⟨t, ht, he⟩)
      · exact Or.inl (Or.inl h)
      · cases t with
        | zero => exact Or.inl (Or.inr (by simpa using he))
        | succ t =>
          refine Or.inr ⟨t, by omega, ?_⟩
          convert he using 1 <;> ring

theorem markPrime_size (X p : Nat) (a : Array Bool) :
    (markPrime X p a).size = a.size := markLoop_size _ _ _ _

/-- Every iteration of the executed marking loop has an in-range destination. -/
theorem markPrime_index_bound {X p t : Nat} (hp : 0 < p)
    (ht : t < X/p+1-p) : p*(p+t) ≤ X := by
  have h : p+t ≤ X/p := by omega
  simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp h

theorem markPrime_indices {X p n : Nat} (hp : 0 < p) (hn : n ≤ X) :
    (∃ t < X/p+1-p, n = p*(p+t)) ↔ p*p ≤ n ∧ p ∣ n := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Nat.mul_le_mul_left p (by omega), ⟨p+t, rfl⟩⟩
  · rintro ⟨hsmall, k, hk⟩
    have hpk : p ≤ k := by
      apply Nat.le_of_mul_le_mul_left (by simpa [hk] using hsmall) hp
    have hkX : k ≤ X/p := by
      apply (Nat.le_div_iff_mul_le hp).mpr
      simpa [Nat.mul_comm, ← hk] using hn
    refine ⟨k-p, by omega, ?_⟩
    rw [Nat.add_sub_of_le hpk]
    exact hk

theorem markPrime_false {X p n : Nat} (a : Array Bool)
    (hp : 0 < p) (hn : n ≤ X) (hsize : X+1 ≤ a.size) :
    sieveRead (markPrime X p a) n = false ↔
      sieveRead a n = false ∨ (p*p ≤ n ∧ p ∣ n) := by
  rw [markPrime, markLoop_false p p _ a (by omega), markPrime_indices hp hn]

theorem sieveLoop_size (X next fuel : Nat) (a : Array Bool) :
    (sieveLoop X next fuel a).size = a.size := by
  induction fuel generalizing next a with
  | zero => rfl
  | succ fuel ih => simp only [sieveLoop, ih]; split_ifs <;> simp [markPrime_size]

theorem sieveLoop_false (X next fuel : Nat) (a : Array Bool) {n : Nat}
    (hn : n ≤ X) (hsize : X+1 ≤ a.size) :
    sieveRead (sieveLoop X next fuel a) n = false ↔
      sieveRead a n = false ∨
      ∃ p, next ≤ p ∧ p < next+fuel ∧ Nat.Prime p ∧ p*p ≤ n ∧ p ∣ n := by
  induction fuel generalizing next a with
  | zero =>
    simp only [sieveLoop, Nat.add_zero]
    constructor
    · exact Or.inl
    · rintro (h | ⟨p, hp0, hp1, _⟩)
      · exact h
      · omega
  | succ fuel ih =>
    simp only [sieveLoop]
    split_ifs with hbase
    · have hprime : Nat.Prime next := (basePrime_correct next).mp hbase
      rw [ih (next+1) (markPrime X next a) (by simpa [markPrime_size] using hsize), markPrime_false a hprime.pos hn hsize]
      constructor
      · rintro ((h | ⟨hs, hd⟩) | ⟨p, hp0, hp1, hpp, hs, hd⟩)
        · exact Or.inl h
        · exact Or.inr ⟨next, by omega, by omega, hprime, hs, hd⟩
        · exact Or.inr ⟨p, by omega, by omega, hpp, hs, hd⟩
      · rintro (h | ⟨p, hp0, hp1, hpp, hs, hd⟩)
        · exact Or.inl (Or.inl h)
        · by_cases he : p = next
          · subst p; exact Or.inl (Or.inr ⟨hs, hd⟩)
          · exact Or.inr ⟨p, by omega, by omega, hpp, hs, hd⟩
    · have hprime : ¬Nat.Prime next := fun h => hbase ((basePrime_correct next).mpr h)
      rw [ih (next+1) a hsize]
      constructor
      · rintro (h | ⟨p, hp0, hp1, hpp, hs, hd⟩)
        · exact Or.inl h
        · exact Or.inr ⟨p, by omega, by omega, hpp, hs, hd⟩
      · rintro (h | ⟨p, hp0, hp1, hpp, hs, hd⟩)
        · exact Or.inl h
        · have hne : p ≠ next := by intro he; exact hprime (he ▸ hpp)
          exact Or.inr ⟨p, by omega, by omega, hpp, hs, hd⟩

theorem sieveInitial_size (X : Nat) : (sieveInitial X).size = X+1 := by
  simp [sieveInitial]

theorem sieveInitial_false {X n : Nat} (hn : n ≤ X) :
    sieveRead (sieveInitial X) n = false ↔ n < 2 := by
  rw [sieveInitial, sieveRead_set_false (by simp; omega), sieveRead_set_false (by simp; omega)]
  simp [sieveRead, Array.getElem?_replicate, show n < X+1 by omega]
  omega

theorem primeSieve_size (X : Nat) : (primeSieve X).size = X+1 := by
  simp [primeSieve, sieveLoop_size, sieveInitial_size]

theorem composite_small_factor {n : Nat} (hn : 2 ≤ n) (hnot : ¬Nat.Prime n) :
    ∃ p, Nat.Prime p ∧ p*p ≤ n ∧ p ∣ n := by
  refine ⟨n.minFac, Nat.minFac_prime (by omega), ?_, Nat.minFac_dvd n⟩
  simpa [Nat.pow_two] using Nat.minFac_sq_le_self (by omega : 0 < n) hnot

theorem primeSieve_false {X n : Nat} (hn : n ≤ X) :
    sieveRead (primeSieve X) n = false ↔ ¬Nat.Prime n := by
  rw [primeSieve, sieveLoop_false X 2 _ _ hn (by simp [sieveInitial_size]), sieveInitial_false hn]
  constructor
  · rintro (hsmall | ⟨p, hp0, hp1, hprime, hs, hd⟩)
    · exact fun hp => by have := hp.two_le; omega
    · intro hprimeN
      obtain h1 | he := hprimeN.eq_one_or_self_of_dvd p hd
      · omega
      · subst p
        have : 2 ≤ n := hprimeN.two_le
        nlinarith
  · intro hnot
    by_cases hsmall : n < 2
    · exact Or.inl hsmall
    · obtain ⟨p, hp, hs, hd⟩ := composite_small_factor (by omega) hnot
      have hpX : p ≤ Nat.sqrt X := Nat.le_sqrt.mpr (hs.trans hn)
      refine Or.inr ⟨p, hp.two_le, ?_, hp, hs, hd⟩
      omega

theorem primeSieve_true {X n : Nat} (hn : n ≤ X) :
    sieveRead (primeSieve X) n = true ↔ Nat.Prime n := by
  have h := primeSieve_false hn
  cases hv : sieveRead (primeSieve X) n <;> simp_all


end FKSComputationLed.Sieve
