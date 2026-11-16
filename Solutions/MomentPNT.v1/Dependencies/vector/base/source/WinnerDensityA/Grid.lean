/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.Moment
open Set
namespace WinnerDensityA

/-- Positive cumulative increments majorize a monotone function at every point,
including strict cutoff/boundary points. No smoothness or convexity is used. -/
theorem monotone_step {f : ℝ → ℝ} {a : ℕ → ℝ} (hf : Monotone f) (ha : Monotone a)
    (n : ℕ) {b : ℝ} (hb : b ≤ a n) :
    f b ≤ f (a 0) + ∑ i ∈ Finset.range n,
      if a i < b then f (a (i+1)) - f (a i) else 0 := by
  induction n with
  | zero => simpa using hf hb
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : b ≤ a n
    · rw [if_neg (not_lt.mpr hn),add_zero]
      exact ih hn
    · have hnb : a n < b := lt_of_not_ge hn
      rw [if_pos hnb]
      have he : (∑ i ∈ Finset.range n,
          if a i < b then f (a (i+1))-f (a i) else 0) = f (a n)-f (a 0) := by
        calc
          _ = ∑ i ∈ Finset.range n, (f (a (i+1))-f (a i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [if_pos ((ha (by exact_mod_cast (Finset.mem_range.mp hi).le)).trans_lt hnb)]
          _ = _ := by
            have hh := Finset.sum_range_sub' (fun i ↦ -(f (a i))) n
            simpa only [neg_sub_neg,neg_sub] using hh
      rw [he]
      have hh := hf hb
      linarith

/-- A finite-set cumulative grid bound that may use a discontinuous or minimum source envelope. -/
theorem weighted_step {α : Type*} (S : Finset α) (w b : α → ℝ)
    {f : ℝ → ℝ} {a : ℕ → ℝ} (hf : Monotone f) (ha : Monotone a) (n : ℕ)
    (hw : ∀ z ∈ S, 0 ≤ w z) (hb : ∀ z ∈ S, b z ≤ a n) :
    ∑ z ∈ S, w z*f (b z) ≤ f (a 0)*(∑ z ∈ S,w z)+
      ∑ i ∈ Finset.range n, (f (a (i+1))-f (a i))*
        (∑ z ∈ S, if a i < b z then w z else 0) := by
  classical
  have hh := Finset.sum_le_sum (s:=S) (fun z hz ↦
    mul_le_mul_of_nonneg_left (monotone_step hf ha n (hb z hz)) (hw z hz))
  apply hh.trans_eq
  simp_rw [mul_add,Finset.mul_sum]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl; intro z _; ring
  · apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro z _
    split_ifs <;> ring

/-- Replace every actual cumulative weight by its proved source envelope. -/
theorem weighted_step_majorant {α : Type*} (S : Finset α) (w b : α → ℝ)
    {f : ℝ → ℝ} {a : ℕ → ℝ} (hf : Monotone f) (ha : Monotone a) (n : ℕ)
    (hw : ∀ z ∈ S, 0 ≤ w z) (hb : ∀ z ∈ S, b z ≤ a n)
    (Q : ℝ → ℝ) (hf0 : 0 ≤ f (a 0))
    (hbase : (∑ z ∈ S,w z) ≤ Q (a 0))
    (hq : ∀ i<n, (∑ z ∈ S, if a i < b z then w z else 0) ≤ Q (a i)) :
    ∑ z ∈ S,w z*f (b z) ≤ f (a 0)*Q (a 0)+
      ∑ i ∈ Finset.range n, (f (a (i+1))-f (a i))*Q (a i) := by
  apply (weighted_step S w b hf ha n hw hb).trans
  apply add_le_add (mul_le_mul_of_nonneg_left hbase hf0)
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hq i (Finset.mem_range.mp hi))
    (sub_nonneg.mpr (hf (ha (by exact_mod_cast (Nat.le_succ i)))))
end WinnerDensityA
#print axioms WinnerDensityA.weighted_step_majorant
