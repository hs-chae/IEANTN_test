/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMellinPoles
import ExplicitNodalMoments
import ExplicitWindowErrors

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- The first spectral moment actually vanishes, by evenness. -/
theorem integral_id_mul_affineSpectrum (nodes : List ℚ) (m : ℕ) :
    (∫ v : ℝ, v*affineSpectrum nodes m v) = 0 := by
  have heq : (fun v : ℝ => (-v)*affineSpectrum nodes m (-v)) =
      (fun v : ℝ => -(v*affineSpectrum nodes m v)) := by
    funext v
    rw [affineSpectrum_even nodes m]
    ring
  have he := MeasureTheory.integral_neg_eq_self (f := fun v : ℝ => v*affineSpectrum nodes m v) (μ := volume)
  rw [heq,integral_neg] at he
  linarith

private theorem exp_remainder_quadratic (r : ℝ) (hr : |r| ≤ 1) :
    |exp r-1-r| ≤ r^2 := by
  have h := Real.exp_bound hr (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  have heq : exp r-(1+r) = exp r-1-r := by ring
  rw [heq] at h
  nlinarith [sq_nonneg r]

/-- A genuine bound for the pole integral of the actual affine window. The
signed constant and linear terms are integrated exactly; the only loss is
controlled by the actual second absolute moment. -/
theorem windowLaplaceIntegral_error (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (b : ℝ)
    (hsmall : |b| *radius nodes m ≤ 1) :
    |windowLaplaceIntegral nodes m b-nodalF0 nodes m| ≤
      b^2*nodalMu2Upper nodes m := by
  let W := affineSpectrum nodes m
  have hcs := hasCompactSupport_affineSpectrum nodes m hlen hm
  have hi : Integrable (fun v : ℝ => W v*(exp (b*v)-1-b*v)) := by
    apply (show Continuous (fun v : ℝ => W v*(exp (b*v)-1-b*v)) by
      dsimp [W]; fun_prop).integrable_of_hasCompactSupport
    exact hcs.mul_right
  have hl : Integrable (fun v : ℝ => W v*exp (b*v)) := by
    apply (show Continuous (fun v : ℝ => W v*exp (b*v)) by
      dsimp [W]; fun_prop).integrable_of_hasCompactSupport
    exact hcs.mul_right
  have hw : Integrable W := integrable_affineSpectrum nodes m hlen hm
  have hv : Integrable (fun v : ℝ => W v*(b*v)) := by
    apply (show Continuous (fun v : ℝ => W v*(b*v)) by
      dsimp [W]; fun_prop).integrable_of_hasCompactSupport
    exact hcs.mul_right
  have heq : windowLaplaceIntegral nodes m b-nodalF0 nodes m =
      ∫ v : ℝ, W v*(exp (b*v)-1-b*v) := by
    rw [show (fun v : ℝ => W v*(exp (b*v)-1-b*v)) =
      (fun v : ℝ => (W v*exp (b*v)-W v)-W v*(b*v)) by funext v; ring]
    rw [integral_sub (f := fun v : ℝ => W v*exp (b*v)-W v)
      (g := fun v : ℝ => W v*(b*v)) (hl.sub hw) hv,
      integral_sub (f := fun v : ℝ => W v*exp (b*v)) (g := W) hl hw]
    have hlin : (∫ v : ℝ, W v*(b*v)) = 0 := by
      rw [show (fun v : ℝ => W v*(b*v)) =
        (fun v : ℝ => b*(v*affineSpectrum nodes m v)) by funext v; dsimp [W]; ring,
        integral_const_mul,integral_id_mul_affineSpectrum,mul_zero]
    rw [hlin,sub_zero,integral_affineSpectrum nodes m hm]
    rfl
  rw [heq]
  calc
    |∫ v : ℝ, W v*(exp (b*v)-1-b*v)| ≤
        ∫ v : ℝ, |W v*(exp (b*v)-1-b*v)| := abs_integral_le_integral_abs
    _ ≤ ∫ v : ℝ, b^2*(v^2*|W v|) := by
      apply integral_mono hi.abs ((integrable_sq_abs_affineSpectrum nodes m hm).const_mul (b^2))
      intro v
      change |W v*(exp (b*v)-1-b*v)| ≤ b^2*(v^2*|W v|)
      by_cases hw0 : W v = 0
      · simp [hw0]
      have hvR := affineSpectrum_support_subset nodes m hlen hm hw0
      have hvabs : |v| ≤ radius nodes m := abs_le.mpr hvR
      have harg : |b*v| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hvabs (abs_nonneg b)).trans hsmall
      rw [abs_mul]
      calc
        |W v| *|exp (b*v)-1-b*v| ≤ |W v| *(b*v)^2 :=
          mul_le_mul_of_nonneg_left (exp_remainder_quadratic _ harg) (abs_nonneg _)
        _ = b^2*(v^2*|W v|) := by ring
    _ ≤ b^2*nodalMu2Upper nodes m := by
      rw [integral_const_mul]
      change b^2*(∫ v : ℝ, v^2*|affineSpectrum nodes m v|) ≤ b^2*nodalMu2Upper nodes m
      exact mul_le_mul_of_nonneg_left
        (integral_sq_abs_affineSpectrum_le nodes m hlen hm hlast) (sq_nonneg b)

/-- The previous integral bound is consumed by the actual Mellin pole,
with its original normalization; it is not an error-budget hypothesis. -/
theorem mellin_pole_lower (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (d L : ℝ) (hd : 0 ≤ d)
    (hsmall : |d/2| *radius nodes m ≤ 1) :
    d*exp (L/2)*(nodalF0 nodes m-(d/2)^2*nodalMu2Upper nodes m) ≤
      d*exp (L/2)*windowLaplaceIntegral nodes m (d/2) := by
  have h := (abs_sub_le_iff.mp (windowLaplaceIntegral_error nodes m hlen hm hlast (d/2) hsmall)).2
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

#print axioms windowLaplaceIntegral_error
#print axioms mellin_pole_lower
end RH080Next.Explicit
