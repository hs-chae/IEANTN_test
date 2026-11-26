/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open Real Set
namespace RH080Next.Dual

/-- The sine-to-argument ratio decreases on the positive half-period.
This proof uses the genuine concavity of sine, not numerical samples. -/
theorem sine_ratio_order (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ π) (hbpos : 0 < b) :
    a * sin b ≤ b * sin a := by
  have hf : 0 ≤ a / b := div_nonneg ha hbpos.le
  have hfle : a / b ≤ 1 := (div_le_one hbpos).2 hab
  have hc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Icc 0 π from ⟨le_rfl, pi_pos.le⟩)
    (show b ∈ Icc 0 π from ⟨hbpos.le, hb⟩)
    (show 0 ≤ 1 - a / b by linarith) hf (by ring)
  have hh : (a / b) * sin b ≤ sin a := by
    simpa [smul_eq_mul, Real.sin_zero, div_mul_cancel₀ a hbpos.ne'] using hc
  have hk := mul_le_mul_of_nonneg_right hh hbpos.le
  field_simp at hk
  nlinarith

/-- A global supporting line for the square of arccos, expressed without
an inverse trigonometric function. It is valid throughout the half-period. -/
theorem cosine_square_tangent (r t : ℝ) (hr : 0 < r) (hrpi : r < π)
    (ht : 0 ≤ t) (htpi : t ≤ π) :
    r ^ 2 + (2 * r / sin r) * (cos r - cos t) ≤ t ^ 2 := by
  have hs : 0 < sin r := sin_pos_of_pos_of_lt_pi hr hrpi
  let k := 2 * r / sin r
  let f : ℝ → ℝ := fun x => x ^ 2 + k * cos x
  have hd (x : ℝ) : HasDerivAt f (2 * x - k * sin x) x := by
    convert! ((hasDerivAt_id x).pow 2).add ((hasDerivAt_cos x).const_mul k) using 1 <;>
      simp [f] <;> ring
  have ha : AntitoneOn f (Icc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 r)
    · exact (by fun_prop : Continuous f).continuousOn
    · intro x hx; exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi : 0 < x ∧ x < r := by simpa [interior_Icc] using hx
      rw [(hd x).deriv]
      have hratio := sine_ratio_order x r hxi.1.le hxi.2.le hrpi.le hr
      dsimp [k]
      have hq : 2 * x ≤ (2 * r * sin x) / sin r :=
        (le_div_iff₀ hs).2 (by nlinarith)
      rw [div_mul_eq_mul_div]
      linarith
  have hm : MonotoneOn f (Icc r π) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc r π)
    · exact (by fun_prop : Continuous f).continuousOn
    · intro x hx; exact (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      have hxi : r < x ∧ x < π := by simpa [interior_Icc] using hx
      rw [(hd x).deriv]
      have hratio := sine_ratio_order r x hr.le hxi.1.le hxi.2.le (lt_trans hr hxi.1)
      dsimp [k]
      have hq : (2 * r * sin x) / sin r ≤ 2 * x :=
        (div_le_iff₀ hs).2 (by nlinarith)
      rw [div_mul_eq_mul_div]
      linarith
  have hmin : f r ≤ f t := by
    by_cases htr : t ≤ r
    · exact ha ⟨ht, htr⟩ ⟨hr.le, le_rfl⟩ htr
    · exact hm ⟨le_rfl, hrpi.le⟩ ⟨le_of_not_ge htr, htpi⟩ (le_of_not_ge htr)
  dsimp [f, k] at hmin
  nlinarith

#print axioms sine_ratio_order
#print axioms cosine_square_tangent
end RH080Next.Dual
