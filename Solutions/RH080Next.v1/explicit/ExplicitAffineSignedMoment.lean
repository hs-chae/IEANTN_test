/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFiniteDifference
import ExplicitNodalMoments

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def nodalSignedLogUpper (nodes : List ℚ) (m : ℕ) (τ : ℝ) : ℝ :=
  nodalV1 nodes m/(2*π^2) - 2*nodalF0 nodes m*τ*(1-log τ) +
    40*nodalMu2Upper nodes m*τ^3*(1/9-log τ/3)

theorem affineSpectrum_inverse_center_lower (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (u : ℝ) :
    nodalF0 nodes m - 2*π^2*nodalMu2Upper nodes m*u^2 ≤
      inverseCosine (affineSpectrum nodes m) u := by
  rw [← integral_affineSpectrum nodes m hm]
  exact inverseCosine_center_lower (affineSpectrum nodes m)
    (integrable_affineSpectrum nodes m hlen hm) (integrable_sq_abs_affineSpectrum nodes m hm)
    _ (integral_sq_abs_affineSpectrum_le nodes m hlen hm hlast) u

theorem integrable_signed_log_affine_inverse (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) :
    Integrable (fun u : ℝ => |inverseCosine (affineSpectrum nodes m) u| *log |u|) := by
  apply integrable_signed_log_of_continuous_even_tail _
    (continuous_inverseCosine _ (integrable_affineSpectrum nodes m hlen hm))
    (inverseCosine_even _) (nodalV1 nodes m/(4*π^2))
  intro u hu
  have h := inverseCosine_affineSpectrum_variation_bound nodes m hlen hm hlast u (by linarith)
  convert h using 1 <;> field_simp <;> ring

/-- Every premise here is elementary window data. The Fourier amplitude and the
signed logarithmic moment are actual integrals; no moment or decay certificate
is assumed. -/
theorem signed_log_affine_inverse_le (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u| *log |u|) ≤
      nodalSignedLogUpper nodes m τ := by
  have hμ : 0 ≤ nodalMu2Upper nodes m :=
    (integral_nonneg (fun v => mul_nonneg (sq_nonneg v) (abs_nonneg _))).trans
      (integral_sq_abs_affineSpectrum_le nodes m hlen hm hlast)
  have ht : ∀ u : ℝ, 1 < u → |inverseCosine (affineSpectrum nodes m) u| ≤
      (nodalV1 nodes m/(4*π^2))/u^2 := by
    intro u hu
    have h := inverseCosine_affineSpectrum_variation_bound nodes m hlen hm hlast u (by linarith)
    convert h using 1 <;> field_simp <;> ring
  exact signed_log_moment_fourier_bound_40 _ _ _ _ τ (inverseCosine_even _) hτ hτ1 hμ
    (integrableOn_signed_log_of_continuous_tail _
      (continuous_inverseCosine _ (integrable_affineSpectrum nodes m hlen hm)) _ ht)
    (fun u hu => affineSpectrum_inverse_center_lower nodes m hlen hm hlast u)
    (fun u hu => inverseCosine_affineSpectrum_variation_bound nodes m hlen hm hlast u (by linarith))

/-- The cutoff used by the recorded explicit calculation. -/
theorem signed_log_affine_inverse_three_eighths (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) :
    (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u| *log |u|) ≤
      nodalSignedLogUpper nodes m (3/8) :=
  signed_log_affine_inverse_le nodes m hlen hm hlast (3/8) (by norm_num) (by norm_num)

end RH080Next.Explicit
