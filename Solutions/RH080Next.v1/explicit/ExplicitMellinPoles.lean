/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCompactLaplace
import ExplicitMellinArithmetic

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def windowLaplaceIntegral (nodes : List ℚ) (m : ℕ) (b : ℝ) : ℝ :=
  ∫ v : ℝ, affineSpectrum nodes m v*exp (b*v)

/-- Actual imaginary endpoint values of the very same entire function used
in CMS6, proved by uniqueness and the compact Fourier-Laplace integral. -/
theorem mellinTest_imaginary_value (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L y : ℝ) :
    mellinTest H d L (-(y:ℂ)*Complex.I) =
      ((d*exp (L*y)*windowLaplaceIntegral nodes m (d*y):ℝ):ℂ) := by
  have hEq := entire_extension_eq_compactLaplace nodes m hlen hm H hH hreal
  unfold mellinTest
  rw [hEq]
  have harg : (((d/(2*π):ℝ):ℂ))*(-(y:ℂ)*Complex.I) =
      -((d*y/(2*π):ℝ):ℂ)*Complex.I := by push_cast; ring
  have hphase : Complex.I*(L:ℂ)*(-(y:ℂ)*Complex.I) = ((L*y:ℝ):ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [harg,compactLaplace_negative_imag,hphase,←Complex.ofReal_exp]
  have hint : (∫ v in Icc (-radius nodes m) (radius nodes m),
      affineSpectrum nodes m v*exp (2*π*(d*y/(2*π))*v)) =
      windowLaplaceIntegral nodes m (d*y) := by
    have heq : (fun v : ℝ => affineSpectrum nodes m v*exp (2*π*(d*y/(2*π))*v)) =
        (fun v : ℝ => affineSpectrum nodes m v*exp ((d*y)*v)) := by
      funext v
      congr 2
      field_simp
    rw [heq]
    unfold windowLaplaceIntegral
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    have hw : affineSpectrum nodes m v = 0 := by
      by_contra h
      exact hv (affineSpectrum_support_subset nodes m hlen hm h)
    rw [hw,zero_mul]
  rw [hint]
  push_cast
  ring

#print axioms mellinTest_imaginary_value
end RH080Next.Explicit
