/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineWindow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

theorem hat_eq_indicators (x : ℝ) :
    hat x = (Ioc (-1 : ℝ) 0).indicator (fun u : ℝ => 1 + u) x +
      (Ioc (0 : ℝ) 1).indicator (fun u : ℝ => 1 - u) x := by
  by_cases hL : x ∈ Ioc (-1 : ℝ) 0
  · have hR : x ∉ Ioc (0 : ℝ) 1 := by
      intro h
      exact (not_lt_of_ge hL.2) h.1
    rw [indicator_of_mem hL, indicator_of_notMem hR]
    rw [hat, abs_of_nonpos hL.2, max_eq_right (by linarith [hL.1])]
    ring
  · by_cases hR : x ∈ Ioc (0 : ℝ) 1
    · rw [indicator_of_notMem hL, indicator_of_mem hR]
      rw [hat, abs_of_pos hR.1, max_eq_right (by linarith [hR.2])]
      ring
    · rw [indicator_of_notMem hL, indicator_of_notMem hR]
      rw [hat, max_eq_left]
      · norm_num
      · simp only [mem_Ioc, not_and_or, not_lt, not_le] at hL hR
        rcases le_or_gt x 0 with hx | hx
        · rw [abs_of_nonpos hx]
          rcases hL with h | h <;> linarith
        · rw [abs_of_pos hx]
          rcases hR with h | h <;> linarith

private theorem pow_mul_hat_eq_indicators (k : ℕ) :
    (fun u : ℝ => u ^ k * hat u) =
      (fun u : ℝ => (Ioc (-1 : ℝ) 0).indicator (fun v : ℝ => v ^ k + v ^ (k+1)) u +
        (Ioc (0 : ℝ) 1).indicator (fun v : ℝ => v ^ k - v ^ (k+1)) u) := by
  funext u
  rw [hat_eq_indicators]
  by_cases hL : u ∈ Ioc (-1 : ℝ) 0 <;> by_cases hR : u ∈ Ioc (0 : ℝ) 1 <;>
    simp [hL, hR, Set.indicator, pow_succ] <;> ring

theorem integrable_pow_mul_hat (k : ℕ) : Integrable (fun u : ℝ => u ^ k * hat u) := by
  rw [pow_mul_hat_eq_indicators]
  apply Integrable.add
  · exact (((continuous_id.pow k).add (continuous_id.pow (k+1))).integrableOn_Ioc).integrable_indicator measurableSet_Ioc
  · exact (((continuous_id.pow k).sub (continuous_id.pow (k+1))).integrableOn_Ioc).integrable_indicator measurableSet_Ioc

theorem integral_pow_mul_hat (k : ℕ) :
    (∫ u : ℝ, u ^ k * hat u) = ((-1 : ℝ) ^ k + 1) / (((k : ℝ) + 1) * (k + 2)) := by
  have hL : Integrable ((Ioc (-1 : ℝ) 0).indicator (fun v : ℝ => v ^ k + v ^ (k+1))) :=
    (((continuous_id.pow k).add (continuous_id.pow (k+1))).integrableOn_Ioc).integrable_indicator measurableSet_Ioc
  have hR : Integrable ((Ioc (0 : ℝ) 1).indicator (fun v : ℝ => v ^ k - v ^ (k+1))) :=
    (((continuous_id.pow k).sub (continuous_id.pow (k+1))).integrableOn_Ioc).integrable_indicator measurableSet_Ioc
  rw [pow_mul_hat_eq_indicators, integral_add hL hR,
    integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 0),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_add (f := fun x : ℝ => x ^ k) (g := fun x : ℝ => x ^ (k+1)) ((continuous_id.pow k).intervalIntegrable (-1) 0)
      ((continuous_id.pow (k+1)).intervalIntegrable (-1) 0),
    intervalIntegral.integral_sub (f := fun x : ℝ => x ^ k) (g := fun x : ℝ => x ^ (k+1)) ((continuous_id.pow k).intervalIntegrable 0 1)
      ((continuous_id.pow (k+1)).intervalIntegrable 0 1)]
  rw [integral_pow, integral_pow, integral_pow, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero _), one_pow, zero_sub, sub_zero,
    Nat.cast_add, Nat.cast_one, pow_succ]
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
  field_simp [hk1, hk2]
  ring

@[simp] theorem integral_hat : (∫ u : ℝ, hat u) = 1 := by
  simpa using integral_pow_mul_hat 0

@[simp] theorem integral_id_mul_hat : (∫ u : ℝ, u * hat u) = 0 := by
  simpa using integral_pow_mul_hat 1

@[simp] theorem integral_sq_mul_hat : (∫ u : ℝ, u ^ 2 * hat u) = 1 / 6 := by
  have h := integral_pow_mul_hat 2
  norm_num at h ⊢
  exact h

end RH080Next.Explicit
