/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Explicit

/-- Actual prime integers in the left-open, right-closed real interval. -/
def realPrimesIoc (a b : ℝ) : Finset ℕ := Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊

theorem mem_realPrimesIoc (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (p : ℕ) :
    p ∈ realPrimesIoc a b ↔ Nat.Prime p ∧ a < (p:ℝ) ∧ (p:ℝ) ≤ b := by
  simp only [realPrimesIoc,Finset.mem_sdiff,Nat.mem_primesLE,Nat.le_floor_iff hb,Nat.le_floor_iff ha]
  constructor
  · rintro ⟨⟨hpB,hprime⟩,hnot⟩
    refine ⟨hprime,?_,hpB⟩
    by_contra hh
    exact hnot ⟨le_of_not_gt hh,hprime⟩
  · rintro ⟨hprime,hpa,hpb⟩
    exact ⟨⟨hpb,hprime⟩,fun h => (not_lt_of_ge h.1) hpa⟩

theorem realPrimesIoc_card (a b : ℝ) (hab : a ≤ b) :
    (realPrimesIoc a b).card = Nat.primeCounting ⌊b⌋₊-Nat.primeCounting ⌊a⌋₊ := by
  rw [realPrimesIoc,Finset.card_sdiff_of_subset (Nat.primesLE_mono (Nat.floor_mono hab)),
    Nat.primesLE_card_eq_primeCounting,Nat.primesLE_card_eq_primeCounting]

/-- Original general literature input: Montgomery--Vaughan, The large sieve
(1973), Theorem 2, printed p.121, equations (1.10)/(1.12), modulus-one
specialization. CMS1708.04122v2 prints the strict version as (6.10), not (6.8).
The weaker non-strict bound suffices here. Actual floor prime counts preserve
the exact left-open/right-closed real endpoint convention. -/
def SourceMontgomeryVaughan : Prop :=
  ∀ a y : ℝ, 1 < a → 1 < y →
    ((Nat.primeCounting ⌊a+y⌋₊-Nat.primeCounting ⌊a⌋₊:ℕ):ℝ) ≤ 2*y/log y

/-- One enlarged interval gives exactly the same density and entrance
allowances as a cover by blocks of length ell. No floor-cover algorithm,
component-count oracle or endpoint shift is needed. -/
theorem mv_interval_entrance_bound (hMV : SourceMontgomeryVaughan)
    (a b ell : ℝ) (ha : 1 < a) (hab : a ≤ b) (hell : 1 < ell) :
    ((realPrimesIoc a b).card:ℝ) ≤ 2*(b-a)/log ell+2*ell/log ell := by
  let y := b-a+ell
  have hy : 1 < y := by dsimp [y]; linarith
  have hyell : ell ≤ y := by dsimp [y]; linarith
  have hsub : realPrimesIoc a b ⊆ realPrimesIoc a (a+y) := by
    intro p hp
    have hm := (mem_realPrimesIoc a b (by linarith) (by linarith) p).mp hp
    apply (mem_realPrimesIoc a (a+y) (by linarith) (by dsimp [y]; linarith) p).mpr
    exact ⟨hm.1,hm.2.1,hm.2.2.trans (by dsimp [y]; linarith)⟩
  have hcard : ((realPrimesIoc a b).card:ℝ) ≤ ((realPrimesIoc a (a+y)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hs := hMV a y ha hy
  rw [←realPrimesIoc_card a (a+y) (by dsimp [y]; linarith)] at hs
  have hlog : log ell ≤ log y := log_le_log (by linarith) hyell
  have hquot : 2*y/log y ≤ 2*y/log ell :=
    div_le_div_of_nonneg_left (by dsimp [y]; positivity) (log_pos hell) hlog
  calc
    ((realPrimesIoc a b).card:ℝ) ≤ ((realPrimesIoc a (a+y)).card:ℝ) := hcard
    _ ≤ 2*y/log y := hs
    _ ≤ 2*y/log ell := hquot
    _ = _ := by dsimp [y]; ring

/-- The same exact source bound applies to any finite set of actual primes
inside the physical interval, as needed by finite atomic wing measures. -/
theorem mv_finite_prime_interval_bound (hMV : SourceMontgomeryVaughan)
    (P : Finset ℕ) (a b ell : ℝ) (ha : 1 < a) (hab : a ≤ b) (hell : 1 < ell)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ a < (p:ℝ) ∧ (p:ℝ) ≤ b) :
    (P.card:ℝ) ≤ 2*(b-a)/log ell+2*ell/log ell := by
  have hsub : P ⊆ realPrimesIoc a b := by
    intro p hp
    exact (mem_realPrimesIoc a b (by linarith) (by linarith) p).mpr (hP p hp)
  have hcard : (P.card:ℝ) ≤ ((realPrimesIoc a b).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (mv_interval_entrance_bound hMV a b ell ha hab hell)

#print axioms mv_interval_entrance_bound
#print axioms mv_finite_prime_interval_bound
end RH080Next.Explicit
