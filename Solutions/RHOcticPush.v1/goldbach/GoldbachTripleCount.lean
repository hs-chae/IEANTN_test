/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Goldbach
import QuarticWindow
import Mathlib

/-! Actual sorted ternary Goldbach representation counts. A finite binary
Goldbach theorem and many primes above n/2 give distinct sorted triples, with
injectivity witnessed by their largest (third) prime. No binary theorem is assumed
proved, and this is a conditional finite transfer, not a global existence record. -/
namespace RHOcticPush.Goldbach
open Finset Real Set
set_option maxHeartbeats 0

noncomputable def sortedTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (n + 1)).product ((range (n + 1)).product (range (n + 1)))).filter
    (fun t => t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧
      t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 + t.2.1 + t.2.2 = n)

lemma mem_sortedTriples {n a b p : ℕ} :
    (a, b, p) ∈ sortedTriples n ↔
      a.Prime ∧ b.Prime ∧ p.Prime ∧ a ≤ b ∧ b ≤ p ∧ a + b + p = n := by
  classical
  simp only [sortedTriples, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by change a < n + 1; omega),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by change b < n + 1; omega),
        Finset.mem_range.mpr (by change p < n + 1; omega)⟩⟩

lemma choose_sorted_pair {H m : ℕ} (hEven : IEANTN.GoldbachEvenUpTo H)
    (hm4 : 4 ≤ m) (hmH : m ≤ H) (hm : Even m) :
    ∃ a b : ℕ, a.Prime ∧ b.Prime ∧ a ≤ b ∧ a + b = m := by
  obtain ⟨a, b, ha, hb, hab⟩ := hEven m (Finset.mem_Icc.mpr ⟨hm4, hmH⟩) hm
  by_cases h : a ≤ b
  · exact ⟨a, b, ha, hb, h, hab.symm⟩
  · exact ⟨b, a, hb, ha, by omega, by omega⟩

/-- The representation uses p as largest prime, and the residual lies in the
actual certified binary range[4,H]. Repeated primes are permitted. -/
lemma triple_for_prime {H n p : ℕ} (hEven : IEANTN.GoldbachEvenUpTo H)
    (hn : Odd n) (hp : p.Prime) (hp2 : 2 < p) (hhalf : n < 2 * p)
    (hupper : p + 4 ≤ n) (hres : n - p ≤ H) :
    ∃ t ∈ sortedTriples n, t.2.2 = p := by
  have hpodd : Odd p := hp.odd_of_ne_two (by omega)
  have hm : Even (n - p) := hn.tsub_odd hpodd
  obtain ⟨a, b, ha, hb, hab, hsum⟩ := choose_sorted_pair hEven
    (by omega) hres hm
  refine ⟨(a, b, p), mem_sortedTriples.mpr ⟨ha, hb, hp, hab, ?_, ?_⟩, rfl⟩ <;> omega

/-- A genuine injective finite-program-free transfer: each available largest
prime yields a distinct actual sorted triple. No representations are double-counted. -/
theorem card_le_sortedTriples {H n : ℕ} (hEven : IEANTN.GoldbachEvenUpTo H)
    (hn : Odd n) (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime)
    (hp2 : ∀ p ∈ s, 2 < p)
    (hhalf : ∀ p ∈ s, n < 2 * p)
    (hupper : ∀ p ∈ s, p + 4 ≤ n)
    (hres : ∀ p ∈ s, n - p ≤ H) : s.card ≤ (sortedTriples n).card := by
  classical
  have hex : ∀ p : {p : ℕ // p ∈ s}, ∃ t ∈ sortedTriples n, t.2.2 = p.val :=
    fun p => triple_for_prime hEven hn (hp p p.property) (hp2 p p.property)
      (hhalf p p.property) (hupper p p.property) (hres p p.property)
  choose f hf hlast using hex
  let e : {p : ℕ // p ∈ s} → {t // t ∈ sortedTriples n} := fun p => ⟨f p, hf p⟩
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    have hlast' := congrArg (fun t : {t // t ∈ sortedTriples n} => t.val.2.2) hpq
    change (f p).2.2 = (f q).2.2 at hlast'
    rwa [hlast p, hlast q] at hlast'
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective e he

/-- Exact real-window geometry, including both strict prime-window endpoints. -/
theorem window_card_le_sortedTriples {H n : ℕ}
    (hEven : IEANTN.GoldbachEvenUpTo H) (hn : Odd n) {u v : ℝ}
    (hu2 : 2 ≤ u) (hhalf : (n : ℝ) / 2 < u)
    (hupper : v ≤ (n : ℝ) - 4) (hres : (n : ℝ) - u ≤ (H : ℝ)) :
    (QuarticWindow.primesBetween u v).card ≤ (sortedTriples n).card := by
  apply card_le_sortedTriples hEven hn
  · intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.1
    have h' : (2 : ℝ) < p := hu2.trans_lt h
    exact_mod_cast h'
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.1
    have h' : (n : ℝ) < 2 * p := by linarith
    exact_mod_cast h'
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.2
    have h' : (p : ℝ) + 4 ≤ n := by linarith
    exact_mod_cast h'
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2.1
    have h' : (n : ℝ) ≤ (p : ℝ) + H := by linarith
    have hnat : n ≤ p + H := by exact_mod_cast h'
    omega

#print axioms triple_for_prime
#print axioms card_le_sortedTriples
#print axioms window_card_le_sortedTriples
end RHOcticPush.Goldbach
