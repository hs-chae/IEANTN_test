/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

/-- The derivative of the actual inverse-cosine integral, including at zero. -/
def inverseCosineDerivative (W : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ v : ℝ, W v * (-sin (2*π*u*v) * (2*π*v))

theorem cosine_derivative_integrand_bound (W : ℝ → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hsupp : Function.support W ⊆ Icc (-R) R) (u v : ℝ) :
    ‖W v * (-sin (2*π*u*v) * (2*π*v))‖ ≤ (2*π*R)*|W v| := by
  by_cases hv : W v = 0
  · simp [hv]
  · have hvr : |v| ≤ R := abs_le.mpr (hsupp hv)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_mul,
      abs_of_pos (by positivity : 0 < 2*π)]
    calc
      |W v| * (|sin (2*π*u*v)| * (2*π*|v|)) ≤
          |W v| * (1 * (2*π*|v|)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (abs_sin_le_one _) (by positivity)) (abs_nonneg _)
      _ ≤ (2*π*R)*|W v| := by
        nlinarith [mul_le_mul_of_nonneg_left hvr (by positivity : 0≤2*π), abs_nonneg (W v)]

theorem hasDerivAt_inverseCosine_of_support (W : ℝ → ℝ) (R : ℝ)
    (hW : Continuous W) (hi : Integrable W) (hR : 0 ≤ R)
    (hsupp : Function.support W ⊆ Icc (-R) R) (u : ℝ) :
    HasDerivAt (inverseCosine W) (inverseCosineDerivative W u) u := by
  have hmeas (x : ℝ) : AEStronglyMeasurable
      (fun v : ℝ => W v * cos (2*π*x*v)) := by fun_prop
  have hdmeas (x : ℝ) : AEStronglyMeasurable
      (fun v : ℝ => W v * (-sin (2*π*x*v) * (2*π*v))) := by fun_prop
  have hint : Integrable (fun v : ℝ => W v * cos (2*π*u*v)) := by
    apply hi.abs.mono' (hmeas u)
    filter_upwards [] with v
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (abs_cos_le_one (2*π*u*v)) (abs_nonneg (W v))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x v : ℝ => W v * cos (2*π*x*v))
      (F' := fun x v : ℝ => W v * (-sin (2*π*x*v) * (2*π*v)))
      (bound := fun v : ℝ => (2*π*R)*|W v|)
      (s := Set.univ) (x₀ := u) (by simp)
      (Eventually.of_forall hmeas) hint (hdmeas u)
      (Eventually.of_forall (fun v x _ => cosine_derivative_integrand_bound W R hR hsupp x v))
      (hi.abs.const_mul _) (Eventually.of_forall (fun v x _ => by
        convert ((((hasDerivAt_id x).const_mul (2*π)).mul_const v).cos.const_mul (W v)) using 1 <;> first | rfl | simp only [id_eq, mul_one]))
  simpa only [inverseCosine, inverseCosineDerivative] using! h.2

theorem continuous_inverseCosineDerivative_of_support (W : ℝ → ℝ) (R : ℝ)
    (hW : Continuous W) (hi : Integrable W) (hR : 0 ≤ R)
    (hsupp : Function.support W ⊆ Icc (-R) R) :
    Continuous (inverseCosineDerivative W) := by
  apply continuous_of_dominated (bound := fun v : ℝ => (2*π*R)*|W v|)
  · intro x; fun_prop
  · intro x
    exact Eventually.of_forall (fun v => cosine_derivative_integrand_bound W R hR hsupp x v)
  · exact hi.abs.const_mul _
  · exact Eventually.of_forall (fun v => by fun_prop)

theorem inverseCosineDerivative_bound_of_support (W : ℝ → ℝ) (R : ℝ)
    (hW : Continuous W) (hi : Integrable W) (hR : 0 ≤ R)
    (hsupp : Function.support W ⊆ Icc (-R) R) (u : ℝ) :
    |inverseCosineDerivative W u| ≤ (2*π*R)*(∫ v : ℝ, |W v|) := by
  have hm : AEStronglyMeasurable (fun v : ℝ =>
      ‖W v * (-sin (2*π*u*v) * (2*π*v))‖) := by fun_prop
  have hint := (hi.abs.const_mul (2*π*R)).mono' hm
    (Eventually.of_forall (fun v => by
      simpa only [norm_norm] using cosine_derivative_integrand_bound W R hR hsupp u v))
  calc
    |inverseCosineDerivative W u| ≤
        ∫ v : ℝ, ‖W v * (-sin (2*π*u*v) * (2*π*v))‖ := by
      simpa only [inverseCosineDerivative, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun v : ℝ => W v * (-sin (2*π*u*v) * (2*π*v)))
    _ ≤ ∫ v : ℝ, (2*π*R)*|W v| := integral_mono hint (hi.abs.const_mul _)
      (fun v => cosine_derivative_integrand_bound W R hR hsupp u v)
    _ = _ := integral_const_mul _ _

theorem hasDerivAt_inverseCosine_affineSpectrum (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (u : ℝ) :
    HasDerivAt (inverseCosine (affineSpectrum nodes m))
      (inverseCosineDerivative (affineSpectrum nodes m) u) u :=
  hasDerivAt_inverseCosine_of_support _ (radius nodes m)
    (continuous_affineSpectrum nodes m) (integrable_affineSpectrum nodes m hlen hm)
    (by unfold radius; positivity) (affineSpectrum_support_subset nodes m hlen hm) u

theorem inverseCosine_affineSpectrum_deriv_bound (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (u : ℝ) :
    |deriv (inverseCosine (affineSpectrum nodes m)) u| ≤
      2*π*radius nodes m*nodalMassA0 nodes m := by
  rw [(hasDerivAt_inverseCosine_affineSpectrum nodes m hlen hm u).deriv]
  exact (inverseCosineDerivative_bound_of_support _ (radius nodes m)
    (continuous_affineSpectrum nodes m) (integrable_affineSpectrum nodes m hlen hm)
    (by unfold radius; positivity) (affineSpectrum_support_subset nodes m hlen hm) u).trans
      (mul_le_mul_of_nonneg_left (integral_abs_affineSpectrum_le nodes m hlen hm)
        (by unfold radius; positivity))

theorem continuous_deriv_inverseCosine_affineSpectrum (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) :
    Continuous (deriv (inverseCosine (affineSpectrum nodes m))) := by
  have heq : deriv (inverseCosine (affineSpectrum nodes m)) =
      inverseCosineDerivative (affineSpectrum nodes m) :=
    funext (fun u => (hasDerivAt_inverseCosine_affineSpectrum nodes m hlen hm u).deriv)
  rw [heq]
  exact continuous_inverseCosineDerivative_of_support _ (radius nodes m)
    (continuous_affineSpectrum nodes m) (integrable_affineSpectrum nodes m hlen hm)
    (by unfold radius; positivity) (affineSpectrum_support_subset nodes m hlen hm)

#print axioms hasDerivAt_inverseCosine_affineSpectrum
#print axioms inverseCosine_affineSpectrum_deriv_bound
#print axioms continuous_deriv_inverseCosine_affineSpectrum
end RH080Next.Explicit
