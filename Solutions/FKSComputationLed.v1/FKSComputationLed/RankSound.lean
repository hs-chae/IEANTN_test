/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.NativeRanks
import FKSComputationLed.Support.PrimeSortedMath
import FKSComputationLed.Support.PrimeRankMath
open FKSComputationLed.Sieve
namespace FKSComputationLed.RankSound
open NativeRanks

def values (ps : Array UInt32) : List Nat := ps.toList.map UInt32.toNat
lemma values_get (ps : Array UInt32) (i : Nat) (hi : i<ps.size) :
    (values ps)[i]'(by simpa [values] using hi) = ps[i]!.toNat := by
  simp only [values,List.getElem_map,Array.getElem_toList]
  rw [getElem!_pos ps i hi]
lemma nodup_of_sorted (xs : List Nat) (h : xs.Pairwise (·<·)) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.pairwise_cons] at h
    simp only [List.nodup_cons]
    refine ⟨?_,ih h.2⟩
    intro ha
    have hh := h.1 a ha
    omega
lemma canonical_complete (U : Nat) (hU : U≤2000000000) (p : Nat) :
    p∈values (oddPrimeList U) ↔ Nat.Prime p ∧ 3≤p ∧ p≤U := by
  simp only [values,List.mem_map]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact (SieveMath.oddPrimeList_mem U hU w).mp (by simpa using hw)
  · rintro ⟨hp,h3,hpU⟩
    refine ⟨UInt32.ofNat p,?_,?_⟩
    · simpa using SieveMath.oddPrimeList_complete U p hU hp h3 hpU
    · exact SieveMath.candidate_word_exact hU hpU
lemma canonical_sorted (U : Nat) (hU : U≤2000000000) :
    (values (oddPrimeList U)).Pairwise (·<·) := by
  simpa only [values,List.pairwise_map] using
    SieveMath.oddPrimeList_strictSorted_counter U hU

/-- Boundary checks on the complete canonical list give the actual Mathlib prime count. -/
theorem rankCheck_sound {U n c : Nat} (hU : U≤2000000000)
    (hn : 3≤n) (hnU : n≤U) (hcheck : rankCheck (oddPrimeList U) n c=true) :
    Nat.primeCounting n=c := by
  have h := of_decide_eq_true hcheck
  change 2≤c ∧ c-2<(oddPrimeList U).size ∧
    (oddPrimeList U)[c-2]!.toNat≤n ∧
    (c-1=(oddPrimeList U).size ∨
      (c-1<(oddPrimeList U).size ∧ n<(oddPrimeList U)[c-1]!.toNat)) at h
  let ps := oddPrimeList U
  let xs := values ps
  change 2≤c ∧ c-2<ps.size ∧ ps[c-2]!.toNat≤n ∧
    (c-1=ps.size ∨ (c-1<ps.size ∧ n<ps[c-1]!.toNat)) at h
  have hlen : xs.length=ps.size := by simp [xs,values]
  have hs : xs.Pairwise (·<·) := canonical_sorted U hU
  have hr : c-1≤xs.length := by
    rw [hlen]
    rcases h.2.2.2 with he | he <;> omega
  have hp : ∀ hh : 0<c-1, xs[c-1-1]'(by omega)≤n := by
    intro hh
    have he : c-1-1=c-2 := by omega
    simp only [he]
    rw [values_get ps (c-2) h.2.1]
    exact h.2.2.1
  have hnext : ∀ hh : c-1<xs.length, n<xs[c-1]'hh := by
    intro hh
    have hlt : c-1<ps.size := by simpa only [hlen] using hh
    rw [values_get ps (c-1) hlt]
    rcases h.2.2.2 with he | he
    · omega
    · exact he.2
  have he := RankMath.rank_of_two_boundaries xs n (c-1) hs hr hp hnext
  have hc := RankMath.complete_odd_list_count xs U n hn hnU
    (nodup_of_sorted xs hs) (canonical_complete U hU)
  rw [he] at hc
  omega
#print axioms rankCheck_sound
end FKSComputationLed.RankSound
