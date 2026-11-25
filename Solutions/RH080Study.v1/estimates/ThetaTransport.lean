/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

set_option autoImplicit false
namespace RH080.Estimates
open Real Finset

/-- Same strictly open window as the inherited IEANTN prime-window vocabulary. -/
noncomputable def openPrimes (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter fun p => a < (p : ℝ) ∧ (p : ℝ) < b

/-- The RH theorem of Schoenfeld1976, Theorem10(6.1), theta component.
This is an explicit external source proposition, not a new Lean axiom. -/
def SchoenfeldTheta61 : Prop := RiemannHypothesis → ∀ x : ℝ,
  2300000000 ≤ x → |Chebyshev.theta x - x| <
    sqrt x * (log x - 2) * log x / (8 * π)

/-- Büthe arXiv1511.02032v2, Theorem2(1.6),(1.7). Unconditional
finite computation remains a source premise; this study does not verify its source. -/
def ButheTheta1617 : Prop :=
  (∀ x : ℝ, 1423 ≤ x → x ≤ (10 : ℝ)^19 →
    x - Chebyshev.theta x ≤ (39 / 20 : ℝ) * sqrt x) ∧
  (∀ x : ℝ, 1 ≤ x → x ≤ (10 : ℝ)^19 →
    (1 / 20 : ℝ) * sqrt x < x - Chebyshev.theta x)

/-- Full endpoint bound into strictly open prime counts. The single `log b`
allowance removes a possible prime at the upper endpoint, for every real a,b. -/
theorem theta_sub_le_open_count {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 1 ≤ b) :
    Chebyshev.theta b - Chebyshev.theta a ≤
      (((openPrimes a b).card : ℝ) + 1) * log b := by
  classical
  let A := Nat.primesLE ⌊a⌋₊
  let B := Nat.primesLE ⌊b⌋₊
  let C := B \ A
  have hAB : A ⊆ B := by
    intro p hp
    rcases Nat.mem_primesLE.mp hp with ⟨hpa,hprime⟩
    exact Nat.mem_primesLE.mpr ⟨hpa.trans (Nat.floor_le_floor hab),hprime⟩
  have hC (p : ℕ) (hp : p ∈ C) : a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
    rcases Finset.mem_sdiff.mp hp with ⟨hpb,hpa⟩
    rcases Nat.mem_primesLE.mp hpb with ⟨hpb,hprime⟩
    have hpbreal : (p : ℝ) ≤ b :=
      (show (p : ℝ) ≤ (⌊b⌋₊ : ℝ) by exact_mod_cast hpb).trans (Nat.floor_le (by linarith))
    refine ⟨?_,hpbreal⟩
    by_contra hn
    have hpa' : p ≤ ⌊a⌋₊ := (Nat.le_floor_iff ha).mpr (by linarith)
    exact hpa (Nat.mem_primesLE.mpr ⟨hpa',hprime⟩)
  let U := C.filter fun p : ℕ => (p : ℝ) < b
  let V := C.filter fun p : ℕ => ¬(p : ℝ) < b
  have hU : U = openPrimes a b := by
    ext p
    simp only [U, C, B, A, openPrimes, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hpb,hpa⟩,hp⟩
      have h := hC p (Finset.mem_sdiff.mpr ⟨hpb,hpa⟩)
      exact ⟨hpb,h.1,hp⟩
    · rintro ⟨hpb,hpa,hp⟩
      refine ⟨⟨hpb,?_⟩,hp⟩
      intro hpA
      have hpf := (Nat.mem_primesLE.mp hpA).1
      have : (p : ℝ) ≤ a :=
        (show (p : ℝ) ≤ (⌊a⌋₊ : ℝ) by exact_mod_cast hpf).trans (Nat.floor_le ha)
      linarith
  have hV : V.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp q hq
    rcases Finset.mem_filter.mp hp with ⟨hp,hpb⟩
    rcases Finset.mem_filter.mp hq with ⟨hq,hqb⟩
    have hpc := hC p hp
    have hqc := hC q hq
    have : (p : ℝ) = q := by linarith
    exact_mod_cast this
  have hcard : C.card ≤ (openPrimes a b).card + 1 := by
    have hc := Finset.card_filter_add_card_filter_not (s := C) (p := fun p : ℕ => (p : ℝ) < b)
    change U.card + V.card = C.card at hc
    rw [hU] at hc
    omega
  have hsum : ∑ p ∈ C, log (p : ℝ) ≤ (C.card : ℝ) * log b := by
    calc
      _ ≤ ∑ _p ∈ C, log b := by
        apply Finset.sum_le_sum
        intro p hp
        have hpc := hC p hp
        exact log_le_log (by
          have hpprime := (Nat.mem_primesLE.mp ((Finset.mem_sdiff.mp hp).1)).2
          exact_mod_cast hpprime.pos) hpc.2
      _ = _ := by simp
  have hid : ∑ p ∈ C, log (p : ℝ) = Chebyshev.theta b - Chebyshev.theta a := by
    simpa only [C, B, A, Chebyshev.theta_eq_sum_primesLE] using
      (Finset.sum_sdiff_eq_sub (f := fun p : ℕ => log (p : ℝ)) hAB)
  rw [hid] at hsum
  have hreal : (C.card : ℝ) ≤ (openPrimes a b).card + 1 := by exact_mod_cast hcard
  exact hsum.trans (mul_le_mul_of_nonneg_right hreal (log_nonneg hb))

/-- Reusable transport of two one-sided theta estimates into an actual count. -/
theorem count_from_theta_bounds {a b Ea Eb : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 1 < b)
    (hupper : Chebyshev.theta a ≤ a + Ea)
    (hlower : b - Eb ≤ Chebyshev.theta b) :
    (b - a - Ea - Eb) / log b - 1 ≤ ((openPrimes a b).card : ℝ) := by
  have h := theta_sub_le_open_count ha hab hb.le
  have hl : 0 < log b := log_pos hb
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hl).mpr
  nlinarith

/-- Pointwise lower envelope consumes both actual source inequalities. -/
theorem theta_lower_envelope {x e₁ e₂ : ℝ}
    (h₁ : x - e₁ ≤ Chebyshev.theta x) (h₂ : x - e₂ ≤ Chebyshev.theta x) :
    x - min e₁ e₂ ≤ Chebyshev.theta x := by
  rcases le_total e₁ e₂ with h|h
  · simpa [min_eq_left h] using h₁
  · simpa [min_eq_right h] using h₂

end RH080.Estimates
#print axioms RH080.Estimates.theta_sub_le_open_count
#print axioms RH080.Estimates.count_from_theta_bounds
#print axioms RH080.Estimates.theta_lower_envelope
