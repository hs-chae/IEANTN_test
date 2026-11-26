/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineDerivative
import AffineDerivativeBounds
import ExplicitZeroRemainderIntegrals

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def nodalDerivativeTail (nodes : List ℚ) (m : ℕ) : ℝ :=
  (radius nodes m*nodalV1 nodes m+2*nodalV0 nodes)/(2*π)

def nodalDerivativeCentral (nodes : List ℚ) (m : ℕ) : ℝ :=
  2*π*radius nodes m*nodalMassA0 nodes m

theorem nodalDerivativeTail_nonneg (nodes : List ℚ) (m : ℕ) :
    0 ≤ nodalDerivativeTail nodes m := by
  unfold nodalDerivativeTail radius nodalV1 nodalV0
  positivity

theorem nodalDerivativeCentral_nonneg (nodes : List ℚ) (m : ℕ) :
    0 ≤ nodalDerivativeCentral nodes m := by
  unfold nodalDerivativeCentral radius nodalMassA0
  positivity

/-- Both derivative bounds are genuinely instantiated for the actual F:
central differentiation under the integral and sharp discrete-variation
cancellation, followed by integration over the whole continuous half-line. -/
theorem affine_zero_remainder_integral_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (hlast : node nodes (nodes.length-1) = 0)
    (Δ r : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => ((3/20:ℝ)*log (u/Δ)+3)*
      |deriv (inverseCosine (affineSpectrum nodes m)) u|) (Ioi r) ∧
    (∫ u in Ioi r, ((3/20:ℝ)*log (u/Δ)+3)*
      |deriv (inverseCosine (affineSpectrum nodes m)) u|) ≤
      (3/20:ℝ)*nodalDerivativeTail nodes m+
      ((3/20:ℝ)*log (1/Δ)+3)*(nodalDerivativeCentral nodes m+nodalDerivativeTail nodes m) := by
  apply zero_remainder_integral_le _
    (continuous_deriv_inverseCosine_affineSpectrum nodes m hlen hm)
    (nodalDerivativeCentral nodes m) (nodalDerivativeTail nodes m)
    (nodalDerivativeCentral_nonneg nodes m) (nodalDerivativeTail_nonneg nodes m)
    (fun u hu => inverseCosine_affineSpectrum_deriv_bound nodes m hlen hm u)
    ?_ Δ r hΔ hΔ1 hr
  intro u hu
  have h := Primal.deriv_inverseCosine_affineSpectrum_abs_le nodes m hlen hm hlast u (by linarith)
  convert h using 1 <;> unfold nodalDerivativeTail <;> field_simp <;> ring

/-- The coefficient and factor of two in the original zero-count allowance
are obtained by algebra from the actual remainder integral. -/
theorem affine_zero_remainder_normalized_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (hlast : node nodes (nodes.length-1) = 0)
    (d r : ℝ) (hd : 0 < d) (hd1 : d/(2*π) ≤ 1) (hr : 0 < r) :
    2*d*(∫ u in Ioi r, ((3/20:ℝ)*log (u/(d/(2*π)))+3)*
      |deriv (inverseCosine (affineSpectrum nodes m)) u|) ≤
      d*((3/10:ℝ)*nodalDerivativeTail nodes m+
      (3+(3/20:ℝ)*log (1/(d/(2*π))))*2*
        (nodalDerivativeCentral nodes m+nodalDerivativeTail nodes m)) := by
  have h := (affine_zero_remainder_integral_le nodes m hlen hm hlast (d/(2*π)) r
    (by positivity) hd1 hr).2
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*d)
  nlinarith

#print axioms affine_zero_remainder_integral_le
#print axioms affine_zero_remainder_normalized_le
end RH080Next.Explicit
