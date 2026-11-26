/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTIntegerInterpretation
import FapAffineData
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
open scoped BigOperators
namespace RH080Next.Primal.FapFFTKernel
open RH080Next.FFT RH080Next.FFT.IntegerModel

def realCoefficient (j : Nat) : ℝ := (coefficient j : ℝ)/10000000000000000

def symmetricInput (n d : Nat) (a : Nat → ℂ) (j : Nat) : ℂ :=
  ∑k ∈ Finset.range d, ((if j=k then a k else 0) + (if j=n-k then a k else 0))

private theorem direct_sum (d j : Nat) (a : Nat → ℂ) :
    (∑k ∈ Finset.range d, if j=k then a k else 0) = if j<d then a j else 0 := by
  by_cases hj : j<d
  · rw [if_pos hj, Finset.sum_eq_single j]
    · simp
    · intro k hk different
      simp [Ne.symm different]
    · intro absent
      exact False.elim (absent (Finset.mem_range.mpr hj))
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : j≠k := by intro he; subst j; exact hj (Finset.mem_range.mp hk)
    simp [hne]

private theorem mirror_sum (n d j : Nat) (hn : d≤n) (hj : j<n) (a : Nat → ℂ) :
    (∑k ∈ Finset.range d, if j=n-k then a k else 0) = if n-j<d then a (n-j) else 0 := by
  by_cases hs : n-j<d
  · rw [if_pos hs, Finset.sum_eq_single (n-j)]
    · rw [if_pos (show j=n-(n-j) by omega)]
    · intro k hk different
      have hne : j≠n-k := by have hk' := Finset.mem_range.mp hk; omega
      simp [hne]
    · intro absent
      exact False.elim (absent (Finset.mem_range.mpr hs))
  · rw [if_neg hs]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : j≠n-k := by have hk' := Finset.mem_range.mp hk; omega
    simp [hne]

/-- Exact sparse embedding of the actual integer input, on all consumed cells.
The integer decoder's values outside 0<=j<n are irrelevant to this statement. -/
theorem decode_input_eq_symmetric (n : Nat) (hn : 800≤n) (j : Nat) (hj : j<n) :
    decode (input n j) = symmetricInput n 400 (fun k => (realCoefficient k : ℂ)) j := by
  unfold symmetricInput
  rw [Finset.sum_add_distrib, direct_sum, mirror_sum n 400 j (by omega) hj]
  by_cases hl : j<400
  · have hr : ¬n-j<400 := by omega
    simp only [hl, hr, if_true, if_false, add_zero, input]
    apply Complex.ext <;> simp [decode, realCoefficient, unit] <;> push_cast <;> ring
  · by_cases hr : n-j<400
    · simp only [hl, hr, if_true, if_false, zero_add, input]
      apply Complex.ext <;> simp [decode, realCoefficient, unit] <;> push_cast <;> ring
    · simp [hl, hr, input, decode_zero]

private theorem dirac_norm_sum_le (n k : Nat) (a : ℂ) :
    (∑j ∈ Finset.range n, ‖if j=k then a else 0‖) ≤ ‖a‖ := by
  by_cases hk : k<n
  · rw [Finset.sum_eq_single k]
    · simp
    · intro j hj hne; simp [hne]
    · intro absent; exact False.elim (absent (Finset.mem_range.mpr hk))
  · have hz : (∑j ∈ Finset.range n, ‖if j=k then a else 0‖) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hne : j≠k := by intro he; subst j; exact hk (Finset.mem_range.mp hj)
      simp [hne]
    rw [hz]
    exact norm_nonneg _

/-- A sparse symmetric embedding has mass at most twice its finite coefficient
mass. This harmlessly counts the centre twice and never enumerates n zeros. -/
theorem symmetric_mass_le (n d : Nat) (a : Nat → ℂ) :
    coefficientMass n (symmetricInput n d a) ≤ 2*∑k ∈ Finset.range d, ‖a k‖ := by
  unfold coefficientMass
  calc
    _ ≤ ∑j ∈ Finset.range n, ∑k ∈ Finset.range d,
        (‖if j=k then a k else 0‖ + ‖if j=n-k then a k else 0‖) := by
      apply Finset.sum_le_sum
      intro j hj
      unfold symmetricInput
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => norm_add_le _ _))
    _ = ∑k ∈ Finset.range d, ((∑j ∈ Finset.range n, ‖if j=k then a k else 0‖) +
        ∑j ∈ Finset.range n, ‖if j=n-k then a k else 0‖) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_add_distrib
    _ ≤ ∑k ∈ Finset.range d, (‖a k‖+‖a k‖) := by
      apply Finset.sum_le_sum
      intro k hk
      exact add_le_add (dirac_norm_sum_le n k (a k)) (dirac_norm_sum_le n (n-k) (a k))
    _ = _ := by rw [Finset.sum_add_distrib]; ring

theorem natAbs_cast (z : Int) : (z.natAbs : ℝ) = |(z : ℝ)| := by
  have h := congrArg (fun n : Int => (n : ℝ)) (Int.natCast_natAbs z)
  simpa only [Int.cast_natCast, Int.cast_abs] using h

def massNumerator : Nat := 2*∑j ∈ Finset.range 400, (coefficient j).natAbs

theorem massNumerator_bound : massNumerator ≤ 810000000000000000 := by decide +kernel

theorem input_mass_le (n : Nat) (hn : 800≤n) :
    coefficientMass n (fun j => decode (input n j)) ≤ 81 := by
  have heq : coefficientMass n (fun j => decode (input n j)) =
      coefficientMass n (symmetricInput n 400 (fun k => (realCoefficient k : ℂ))) := by
    unfold coefficientMass
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only
    rw [decode_input_eq_symmetric n hn j (Finset.mem_range.mp hj)]
  rw [heq]
  apply (symmetric_mass_le n 400 _).trans
  have hs : (2:ℝ)*(∑j ∈ Finset.range 400, ‖(realCoefficient j : ℂ)‖) =
      (massNumerator:ℝ)/10000000000000000 := by
    simp only [Complex.norm_real, Real.norm_eq_abs, realCoefficient, abs_div,
      abs_of_pos (by norm_num : (0:ℝ)<10000000000000000)]
    unfold massNumerator
    push_cast
    simp only [← natAbs_cast]
    rw [← Finset.sum_div]
    ring
  rw [hs]
  have hb : (massNumerator:ℝ) ≤ 810000000000000000 := by exact_mod_cast massNumerator_bound
  linarith

#print axioms decode_input_eq_symmetric
#print axioms input_mass_le
end RH080Next.Primal.FapFFTKernel
