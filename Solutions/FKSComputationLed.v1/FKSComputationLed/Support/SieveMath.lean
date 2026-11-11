/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.Support.BaseRuntime
import FKSComputationLed.Support.SieveProof
namespace FKSComputationLed.SieveMath
open FKSComputationLed.Sieve
def maximumBase : Nat := 2000000000
/-- Exact membership invariant for the executable collection loop, including its old prefix. -/
theorem collectOdd_mem (flags : Array Bool) (next remaining : Nat) (acc : Array UInt32)
    (word : UInt32) :
    word ∈ collectOdd flags next remaining acc ↔ word ∈ acc ∨
      ∃ j < remaining, word = UInt32.ofNat (next+2*j) ∧ sieveRead flags (next+2*j) = true := by
  induction remaining generalizing next acc with
  | zero => simp [collectOdd]
  | succ remaining ih =>
    simp only [collectOdd]
    split_ifs with hflag
    · rw [ih]
      simp only [Array.mem_push]
      constructor
      · rintro ((h | h) | ⟨j, hj, hw, hf⟩)
        · exact Or.inl h
        · exact Or.inr ⟨0, by omega, by simpa using h, by simpa using hflag⟩
        · refine Or.inr ⟨j+1, by omega, ?_, ?_⟩
          · simpa only [show next+2*(j+1)=next+2+2*j by omega] using hw
          · simpa only [show next+2*(j+1)=next+2+2*j by omega] using hf
      · rintro (h | ⟨j, hj, hw, hf⟩)
        · exact Or.inl (Or.inl h)
        · cases j with
          | zero => exact Or.inl (Or.inr (by simpa using hw))
          | succ j =>
            refine Or.inr ⟨j, by omega, ?_, ?_⟩
            · simpa only [show next+2+2*j=next+2*(j+1) by omega] using hw
            · simpa only [show next+2+2*j=next+2*(j+1) by omega] using hf

    · rw [ih]
      constructor
      · rintro (h | ⟨j, hj, hw, hf⟩)
        · exact Or.inl h
        · refine Or.inr ⟨j+1, by omega, ?_, ?_⟩
          · simpa only [show next+2*(j+1)=next+2+2*j by omega] using hw
          · simpa only [show next+2*(j+1)=next+2+2*j by omega] using hf
      · rintro (h | ⟨j, hj, hw, hf⟩)
        · exact Or.inl h
        · cases j with
          | zero => exact False.elim (hflag (by simpa using hf))
          | succ j =>
            refine Or.inr ⟨j, by omega, ?_, ?_⟩
            · simpa only [show next+2+2*j=next+2*(j+1) by omega] using hw
            · simpa only [show next+2+2*j=next+2*(j+1) by omega] using hf

theorem collectOdd_size_bound (flags : Array Bool) (next remaining : Nat) (acc : Array UInt32) :
    (collectOdd flags next remaining acc).size ≤ acc.size + remaining := by
  induction remaining generalizing next acc with
  | zero => simp [collectOdd]
  | succ remaining ih =>
    simp only [collectOdd]
    split_ifs
    · have h := ih (next+2) (acc.push (UInt32.ofNat next))
      simp only [Array.size_push] at h
      omega
    · have h := ih (next+2) acc
      omega

theorem oddPrimeList_size_bound (U : Nat) : (oddPrimeList U).size ≤ (U-1)/2 := by
  simpa [oddPrimeList] using collectOdd_size_bound (primeSieve U) 3 ((U-1)/2) #[]

theorem odd_candidate_indices (U p : Nat) :
    (∃ j < (U-1)/2, p = 3+2*j) ↔ 3 ≤ p ∧ p ≤ U ∧ Odd p := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨by omega, by omega, ⟨j+1, by omega⟩⟩
  · rintro ⟨hp, hU, ⟨j, hj⟩⟩
    exact ⟨j-1, by omega, by omega⟩

theorem list_candidate_read_bound (U j : Nat) (hj : j < (U-1)/2) :
    3+2*j < (primeSieve U).size := by
  have hU := (odd_candidate_indices U (3+2*j)).mp ⟨j, hj, rfl⟩ |>.2.1
  rw [primeSieve_size]
  omega

theorem base_upper_fits_word : maximumBase < UInt32.size := by norm_num [maximumBase, UInt32.size]

theorem candidate_word_exact {U p : Nat} (hU : U ≤ maximumBase) (hp : p ≤ U) :
    (UInt32.ofNat p).toNat = p :=
  UInt32.toNat_ofNat_of_lt' (lt_of_le_of_lt (hp.trans hU) base_upper_fits_word)

/-- Soundness and completeness of the actual finite list, not of an external prime oracle. -/
theorem oddPrimeList_mem (U : Nat) (hU : U ≤ maximumBase) (word : UInt32) :
    word ∈ oddPrimeList U ↔ Nat.Prime word.toNat ∧ 3 ≤ word.toNat ∧ word.toNat ≤ U := by
  rw [oddPrimeList, collectOdd_mem]
  simp only [Array.not_mem_empty, false_or]
  constructor
  · rintro ⟨j, hj, he, hf⟩
    have hidx := (odd_candidate_indices U (3+2*j)).mp ⟨j, hj, rfl⟩
    have hd : word.toNat = 3+2*j := by rw [he, candidate_word_exact hU hidx.2.1]
    rw [hd]
    exact ⟨(primeSieve_true hidx.2.1).mp hf, hidx.1, hidx.2.1⟩
  · rintro ⟨hp, h3, hbound⟩
    have hodd : Odd word.toNat := hp.odd_iff.mpr h3
    obtain ⟨j, hj, he⟩ := (odd_candidate_indices U word.toNat).mpr ⟨h3, hbound, hodd⟩
    refine ⟨j, hj, ?_, ?_⟩
    · rw [← he]
      exact UInt32.ofNat_toNat.symm
    · rw [← he]
      exact (primeSieve_true hbound).mpr hp

theorem oddPrimeList_sound (U : Nat) (hU : U ≤ maximumBase) (word : UInt32)
    (hmem : word ∈ oddPrimeList U) : Nat.Prime word.toNat ∧ 3 ≤ word.toNat ∧ word.toNat ≤ U :=
  (oddPrimeList_mem U hU word).mp hmem

theorem oddPrimeList_complete (U p : Nat) (hU : U ≤ maximumBase)
    (hp : Nat.Prime p) (h3 : 3 ≤ p) (hbound : p ≤ U) :
    UInt32.ofNat p ∈ oddPrimeList U := by
  apply (oddPrimeList_mem U hU _).mpr
  rw [candidate_word_exact hU hbound]
  exact ⟨hp, h3, hbound⟩


end FKSComputationLed.SieveMath
