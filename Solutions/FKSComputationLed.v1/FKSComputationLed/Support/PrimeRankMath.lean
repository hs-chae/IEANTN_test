/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import Mathlib

namespace FKSComputationLed.RankMath

theorem rank_of_two_boundaries (xs : List ℕ) (x r : ℕ)
    (hs : xs.Pairwise (· < ·)) (hr : r ≤ xs.length)
    (hprev : ∀ h : 0 < r, xs[r-1]'(by omega) ≤ x)
    (hnext : ∀ h : r < xs.length, x < xs[r]'h) :
    (xs.filter (fun a => decide (a ≤ x))).length = r := by
  have hpw := List.pairwise_iff_getElem.mp hs
  have htake : (xs.take r).filter (fun a => decide (a ≤ x)) = xs.take r := by
    apply List.filter_eq_self.mpr
    intro a ha
    obtain ⟨i, hi, he⟩ := List.mem_take_iff_getElem.mp ha
    have hir : i < r := lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hil : i < xs.length := lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hpr : 0 < r := by omega
    have hh := hprev hpr
    by_cases hie : i = r-1
    · subst i
      simpa [he] using hh
    · have hh' := hpw i (r-1) hil (by omega) (by omega)
      rw [he] at hh'
      exact decide_eq_true (by omega)
  have hdrop : (xs.drop r).filter (fun a => decide (a ≤ x)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨i, hi, he⟩ := List.mem_drop_iff_getElem.mp ha
    have hrl : r < xs.length := by omega
    have hh := hnext hrl
    have hri : r+i < xs.length := by omega
    have hxa : x < a := by
      by_cases hie : i=0
      · subst i
        simp only [Nat.add_zero] at he
        omega
      · have hh' := hpw r (r+i) hrl hri (by omega)
        omega
    simpa using (show ¬ a ≤ x by omega)
  have hh : xs.filter (fun a => decide (a ≤ x)) = xs.take r := by
    calc
      _ = ((xs.take r) ++ (xs.drop r)).filter (fun a => decide (a ≤ x)) := by rw [List.take_append_drop]
      _ = xs.take r := by rw [List.filter_append, htake, hdrop, List.append_nil]
  rw [hh, List.length_take, Nat.min_eq_left hr]

theorem complete_odd_list_count (xs : List ℕ) (U n : ℕ)
    (hn : 3 ≤ n) (hnU : n ≤ U) (hnd : xs.Nodup)
    (hcomplete : ∀ p, p ∈ xs ↔ Nat.Prime p ∧ 3 ≤ p ∧ p ≤ U) :
    1 + (xs.filter (fun p => decide (p ≤ n))).length = Nat.primeCounting n := by
  let ys := xs.filter (fun p => decide (p ≤ n))
  have hys : ∀ p, p ∈ ys.toFinset ↔ Nat.Prime p ∧ 3 ≤ p ∧ p ≤ n := by
    intro p
    simp only [List.mem_toFinset, ys, List.mem_filter, decide_eq_true_eq, hcomplete]
    constructor
    · rintro ⟨⟨hp,h3,hpU⟩,hpn⟩
      exact ⟨hp,h3,hpn⟩
    · rintro ⟨hp,h3,hpn⟩
      exact ⟨⟨hp,h3,hpn.trans hnU⟩,hpn⟩
  have h2 : 2 ∉ ys.toFinset := by rw [hys]; omega
  have he : insert 2 ys.toFinset = n.primesLE := by
    ext p
    simp only [Finset.mem_insert, hys, Nat.mem_primesLE]
    constructor
    · rintro (rfl | ⟨hp,h3,hpn⟩)
      · exact ⟨by omega, Nat.prime_two⟩
      · exact ⟨hpn,hp⟩
    · rintro ⟨hpn,hp⟩
      have := hp.two_le
      by_cases he : p=2
      · exact Or.inl he
      · exact Or.inr ⟨hp,by omega,hpn⟩
  have hc := congrArg Finset.card he
  rw [Finset.card_insert_of_notMem h2, Nat.primesLE_card_eq_primeCounting] at hc
  have hlen : ys.toFinset.card = ys.length := List.toFinset_card_of_nodup (hnd.filter _)
  rw [hlen] at hc
  simpa [ys, Nat.add_comm] using hc

#print axioms rank_of_two_boundaries
#print axioms complete_odd_list_count
end FKSComputationLed.RankMath
