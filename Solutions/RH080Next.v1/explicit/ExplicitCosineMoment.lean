/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineWindow
import ExplicitSignedLogMoment
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

theorem one_sub_cos_le_sq_half (t : ℝ) : 1 - cos t ≤ t ^ 2 / 2 := by
  have hs := Real.abs_sin_le_abs (x := t / 2)
  have hs2 := mul_self_le_mul_self (abs_nonneg (sin (t/2))) hs
  simp only [← pow_two, sq_abs] at hs2
  have hc := Real.cos_two_mul (t/2)
  have he := Real.sin_sq_add_cos_sq (t/2)
  rw [show 2 * (t / 2) = t by ring] at hc
  nlinarith

theorem integrable_cosineIntegrand (W : ℝ → ℝ) (hW : Integrable W) (u : ℝ) :
    Integrable (fun v : ℝ => W v * cos (2 * π * u * v)) := by
  apply hW.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with v
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * π * u * v)

@[simp] theorem inverseCosine_zero (W : ℝ → ℝ) :
    inverseCosine W 0 = ∫ v : ℝ, W v := by simp [inverseCosine]

theorem inverseCosine_even (W : ℝ → ℝ) : Function.Even (inverseCosine W) := by
  intro u
  unfold inverseCosine
  apply integral_congr_ae
  filter_upwards with v
  rw [show 2 * π * (-u) * v = -(2 * π * u * v) by ring, Real.cos_neg]

/-- Real inverse-Fourier amplitude has the quadratic central lower bound used
in the signed logarithmic moment, even when the spectral window is signed. -/
theorem inverseCosine_center_lower (W : ℝ → ℝ) (hW : Integrable W)
    (hW2 : Integrable (fun v : ℝ => v ^ 2 * |W v|)) (μ2 : ℝ)
    (hμ2 : (∫ v : ℝ, v ^ 2 * |W v|) ≤ μ2) (u : ℝ) :
    (∫ v : ℝ, W v) - 2 * π ^ 2 * μ2 * u ^ 2 ≤ inverseCosine W u := by
  have hc := integrable_cosineIntegrand W hW u
  have hd : Integrable (fun v : ℝ => W v * (1 - cos (2 * π * u * v))) := by
    convert hW.sub hc using 1
    funext v
    simp only [Pi.sub_apply]
    ring
  have henv := hW2.const_mul (2 * π ^ 2 * u ^ 2)
  have hp : ∀ v : ℝ, W v * (1 - cos (2 * π * u * v)) ≤
      (2 * π ^ 2 * u ^ 2) * (v ^ 2 * |W v|) := by
    intro v
    have hcos : 0 ≤ 1 - cos (2 * π * u * v) := by linarith [cos_le_one (2 * π * u * v)]
    calc
      W v * (1 - cos (2 * π * u * v)) ≤
          |W v| * (1 - cos (2 * π * u * v)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hcos
      _ ≤ |W v| * ((2 * π * u * v) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left (one_sub_cos_le_sq_half _) (abs_nonneg _)
      _ = (2 * π ^ 2 * u ^ 2) * (v ^ 2 * |W v|) := by ring
  have hi := integral_mono hd henv hp
  have heq : (fun v : ℝ => W v * (1 - cos (2 * π * u * v))) =
      (fun v : ℝ => W v - W v * cos (2 * π * u * v)) := by funext v; ring
  rw [heq, integral_sub hW hc, integral_const_mul] at hi
  have hs := mul_le_mul_of_nonneg_left hμ2 (by positivity : 0 ≤ 2 * π ^ 2 * u ^ 2)
  unfold inverseCosine
  nlinarith

theorem inverseCosine_abs_le_mass (W : ℝ → ℝ) (hW : Integrable W) (u : ℝ) :
    |inverseCosine W u| ≤ ∫ v : ℝ, |W v| := by
  unfold inverseCosine
  calc
    |∫ v : ℝ, W v * cos (2 * π * u * v)| ≤
        ∫ v : ℝ, |W v * cos (2 * π * u * v)| := abs_integral_le_integral_abs
    _ ≤ ∫ v : ℝ, |W v| := by
      apply integral_mono (integrable_cosineIntegrand W hW u).abs hW.abs
      intro v
      dsimp only
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one (2 * π * u * v)) (abs_nonneg (W v))

theorem continuous_inverseCosine (W : ℝ → ℝ) (hW : Integrable W) :
    Continuous (inverseCosine W) := by
  unfold inverseCosine
  apply continuous_of_dominated (bound := fun v : ℝ => |W v|)
  · intro u
    exact (integrable_cosineIntegrand W hW u).aestronglyMeasurable
  · intro u
    filter_upwards with v
    simp only [Real.norm_eq_abs, abs_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one (2 * π * u * v)) (abs_nonneg (W v))
  · exact hW.abs
  · filter_upwards with v
    fun_prop

end RH080Next.Explicit
