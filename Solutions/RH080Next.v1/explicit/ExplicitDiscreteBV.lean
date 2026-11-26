/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace RH080Next.Explicit

/-- Summation by parts, with both end terms retained. -/
theorem finite_abel_identity (f q : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, f i*(q i-q (i+1))) =
      f 0*q 0+(∑ i ∈ Finset.range n, (f (i+1)-f i)*q (i+1))-f n*q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ,ih]
    ring

/-- A finite maximum over an interval, specified independently of any
numerical program or certificate. -/
def tailMaximum (S : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,i => S i
  | n+1,i => max (S i) (tailMaximum S n (i+1))

theorem tailMaximum_le (S : ℕ → ℝ) (n i : ℕ) (B : ℝ)
    (h : ∀ j, i≤j → j ≤ i + n → S j≤B) : tailMaximum S n i≤B := by
  induction n generalizing i with
  | zero => exact h i le_rfl (by omega)
  | succ n ih =>
    exact max_le (h i le_rfl (by omega)) (ih (i+1) (fun j hj hjn => h j (by omega) (by omega)))

theorem le_tailMaximum (S : ℕ → ℝ) (n i : ℕ) : S i≤tailMaximum S n i := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

/-- The finite interval-to-variation inequality. Every contiguous increment
of S is bounded above by C; no lower bound on these increments is assumed.
The conclusion controls arbitrary nonnegative weights by their entrance
height plus positive variation, rather than by the number of cells.

For prime-count applications, S is prime mass minus the continuous
majorant's mass. Passage to an actual affine integral remains a separate
analytic step; this theorem does not assume or assert that passage. -/
theorem finite_interval_positive_variation_bound
    (S f : ℕ → ℝ) (n : ℕ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ i≤n, 0≤f i)
    (hinterval : ∀ i j, i≤j → j≤n → S j-S i≤C) :
    (∑ i ∈ Finset.range n, f i*(S (i+1)-S i)) ≤
      C*(f 0+∑ i ∈ Finset.range n, max 0 (f (i+1)-f i)) := by
  let T : ℕ → ℝ := fun i => tailMaximum S (n-i) i
  let q : ℕ → ℝ := fun i => T i-S i
  have hq (i : ℕ) (hi : i≤n) : 0≤q i ∧ q i≤C := by
    constructor
    · exact sub_nonneg.mpr (le_tailMaximum S (n-i) i)
    · have h := tailMaximum_le S (n-i) i (S i+C) (fun j hij hj => by
        have h' := hinterval i j hij (by omega)
        linarith)
      dsimp [q,T]
      linarith
  have hqn : q n=0 := by simp [q,T,tailMaximum]
  have hT (i : ℕ) (hi : i<n) : T (i+1)≤T i := by
    have he : n-i=(n-(i+1))+1 := by omega
    dsimp [T]
    rw [he,tailMaximum]
    exact le_max_right _ _
  have hsumT : (∑ i ∈ Finset.range n, f i*(T (i+1)-T i))≤0 := by
    apply Finset.sum_nonpos
    intro i hi
    exact mul_nonpos_of_nonneg_of_nonpos (hf i (Finset.mem_range.mp hi).le)
      (sub_nonpos.mpr (hT i (Finset.mem_range.mp hi)))
  have hsumq : (∑ i ∈ Finset.range n, f i*(q i-q (i+1)))≤
      C*(f 0+∑ i ∈ Finset.range n, max 0 (f (i+1)-f i)) := by
    rw [finite_abel_identity,hqn,mul_zero,sub_zero,mul_add,Finset.mul_sum]
    apply add_le_add
    · nlinarith [(hq 0 (Nat.zero_le n)).2,hf 0 (Nat.zero_le n)]
    · apply Finset.sum_le_sum
      intro i hi
      have hqi := hq (i+1) (by have := Finset.mem_range.mp hi; omega)
      calc
        (f (i+1)-f i)*q (i+1) ≤ max 0 (f (i+1)-f i)*q (i+1) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hqi.1
        _ ≤ C*max 0 (f (i+1)-f i) := by
          nlinarith [le_max_left (0:ℝ) (f (i+1)-f i)]
  have heq : (∑ i ∈ Finset.range n, f i*(S (i+1)-S i)) =
      (∑ i ∈ Finset.range n, f i*(T (i+1)-T i))+
        ∑ i ∈ Finset.range n, f i*(q i-q (i+1)) := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    ring
  rw [heq]
  linarith

#print axioms finite_abel_identity
#print axioms finite_interval_positive_variation_bound
end RH080Next.Explicit
