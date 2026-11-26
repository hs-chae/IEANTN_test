/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitHatIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem hasDerivAt_hatCosineLeft (t x : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun v : ℝ => (1+v)*sin (t*v)/t + cos (t*v)/t^2)
      ((1+x)*cos (t*x)) x := by
  have hs := ((hasDerivAt_id x).const_mul t).sin
  have hc := ((hasDerivAt_id x).const_mul t).cos
  have hl := (hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)
  have h := (hl.mul hs).div_const t
  have h := h.add (hc.div_const (t^2))
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq, mul_one, zero_add, zero_sub] at h
  apply h.congr_deriv
  field_simp [ht]
  <;> ring

private theorem hasDerivAt_hatCosineRight (t x : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun v : ℝ => (1-v)*sin (t*v)/t - cos (t*v)/t^2)
      ((1-x)*cos (t*x)) x := by
  have hs := ((hasDerivAt_id x).const_mul t).sin
  have hc := ((hasDerivAt_id x).const_mul t).cos
  have h := ((((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).mul hs).div_const t)
  have h := h.sub (hc.div_const (t^2))
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, id_eq, mul_one, zero_add, zero_sub] at h
  apply h.congr_deriv
  field_simp [ht]
  <;> ring

private theorem integral_hatCosineLeft (t : ℝ) (ht : t ≠ 0) :
    (∫ v in (-1:ℝ)..0, (1+v)*cos (t*v)) = (1-cos t)/t^2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun v : ℝ => (1+v)*sin (t*v)/t + cos (t*v)/t^2)
    (f' := fun v : ℝ => (1+v)*cos (t*v)) (by norm_num : (-1:ℝ) ≤ 0)
    (by fun_prop)
    (fun x hx => hasDerivAt_hatCosineLeft t x ht)
    ((by fun_prop : Continuous (fun v : ℝ => (1+v)*cos (t*v))).intervalIntegrable (-1) 0)
  rw [h]
  simp only [mul_zero, sin_zero, cos_zero, mul_one, add_neg_cancel, sub_self, zero_mul, zero_div, zero_add, zero_sub, mul_neg, cos_neg]
  ring

private theorem integral_hatCosineRight (t : ℝ) (ht : t ≠ 0) :
    (∫ v in (0:ℝ)..1, (1-v)*cos (t*v)) = (1-cos t)/t^2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun v : ℝ => (1-v)*sin (t*v)/t - cos (t*v)/t^2)
    (f' := fun v : ℝ => (1-v)*cos (t*v)) (by norm_num : (0:ℝ) ≤ 1)
    (by fun_prop)
    (fun x hx => hasDerivAt_hatCosineRight t x ht)
    ((by fun_prop : Continuous (fun v : ℝ => (1-v)*cos (t*v))).intervalIntegrable 0 1)
  rw [h]
  simp only [mul_zero, sin_zero, cos_zero, mul_one, add_neg_cancel, sub_self, zero_mul, zero_div, zero_add, zero_sub, mul_neg, cos_neg]
  ring

theorem integral_hat_mul_cos (t : ℝ) (ht : t ≠ 0) :
    (∫ v : ℝ, hat v * cos (t*v)) = 2*(1-cos t)/t^2 := by
  have heq : (fun v : ℝ => hat v*cos (t*v)) = (fun v : ℝ =>
      (Ioc (-1:ℝ) 0).indicator (fun x : ℝ => (1+x)*cos (t*x)) v +
      (Ioc (0:ℝ) 1).indicator (fun x : ℝ => (1-x)*cos (t*x)) v) := by
    funext v
    rw [hat_eq_indicators]
    by_cases hL : v ∈ Ioc (-1:ℝ) 0 <;> by_cases hR : v ∈ Ioc (0:ℝ) 1 <;>
      simp [hL,hR,Set.indicator] <;> ring
  have hiL : Integrable ((Ioc (-1:ℝ) 0).indicator (fun x : ℝ => (1+x)*cos (t*x))) :=
    (by fun_prop : Continuous (fun x : ℝ => (1+x)*cos (t*x))).integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  have hiR : Integrable ((Ioc (0:ℝ) 1).indicator (fun x : ℝ => (1-x)*cos (t*x))) :=
    (by fun_prop : Continuous (fun x : ℝ => (1-x)*cos (t*x))).integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  rw [heq, integral_add hiL hiR, integral_indicator measurableSet_Ioc,
    integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 0),
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_hatCosineLeft t ht, integral_hatCosineRight t ht]
  ring

/-- The continuous value at zero is included in the actual hat transform. -/
theorem integral_hat_mul_cos_eq_sinc_sq (t : ℝ) :
    (∫ v : ℝ, hat v*cos (t*v)) = Real.sinc (t/2)^2 := by
  by_cases ht : t = 0
  · subst t
    simpa using integral_hat
  · have ht2 : t/2 ≠ 0 := div_ne_zero ht (by norm_num)
    rw [integral_hat_mul_cos t ht, Real.sinc_of_ne_zero ht2]
    have hc := Real.cos_two_mul (t/2)
    have hs := Real.sin_sq_add_cos_sq (t/2)
    rw [show 2*(t/2) = t by ring] at hc
    have hcos : 1-cos t = 2*sin (t/2)^2 := by nlinarith
    rw [hcos]
    field_simp
    <;> ring

end RH080Next.Explicit
