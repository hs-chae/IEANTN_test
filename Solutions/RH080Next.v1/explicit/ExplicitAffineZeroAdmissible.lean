/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineZeroRemainder
import ExplicitMellinZeroBound
import ExplicitZeroBoundary
import ExplicitTruncatedLogDensity

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

private theorem affine_tail_nonzero (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (hlast : node nodes (nodes.length-1) = 0)
    (u : ℝ) (hu : u ≠ 0) :
    |inverseCosine (affineSpectrum nodes m) u| ≤ (nodalV1 nodes m/(4*π^2))/u^2 := by
  convert inverseCosine_affineSpectrum_variation_bound nodes m hlen hm hlast u hu using 1 <;>
    field_simp <;> ring

/-- ALL admissibility obligations for applying the general CMS summation-by-
parts proof scheme to the actual affine inverse are discharged: actual C1
regularity, evenness, both quadratic tails, both actual integrals and both
vanishing infinity boundaries. Only the published general count input remains
as an analytic source parameter, not a window-specific zero-error premise. -/
theorem affine_CMSZeroAdmissible (hcount : SourceCMSZeroCounting)
    (nodes : List ℚ) (m : ℕ) (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0)
    (d T0 : ℝ) (hd : 0 < d) (hd1 : d ≤ (1/10:ℝ))
    (hT0e : exp 1 ≤ T0) (hT010 : T0 < 10) :
    CMSZeroAdmissible (inverseCosine (affineSpectrum nodes m))
      (deriv (inverseCosine (affineSpectrum nodes m))) (d/(2*π)) T0 := by
  let F := inverseCosine (affineSpectrum nodes m)
  let Δ := d/(2*π)
  let g0 := nodalV1 nodes m/(4*π^2)
  let g1 := nodalDerivativeTail nodes m
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ1 : Δ ≤ 1 := by
    have hp := Real.pi_gt_three
    dsimp [Δ]
    apply (div_le_one (by positivity : 0 < 2*π)).mpr
    linarith
  have hT0 : 0 < T0 := (exp_pos 1).trans_le hT0e
  have hr : 0 < Δ*T0 := mul_pos hΔ hT0
  have hr1 : Δ*T0 ≤ 1 := by
    have hp := Real.pi_gt_three
    have he : Δ*T0*(2*π) = d*T0 := by dsimp [Δ]; field_simp <;> ring
    have hh : d*T0 ≤ 1 := by nlinarith
    nlinarith
  have hg0 : 0 ≤ g0 := by dsimp [g0]; unfold nodalV1; positivity
  have hg1 : 0 ≤ g1 := nodalDerivativeTail_nonneg nodes m
  have htail : ∀ u : ℝ, u ≠ 0 → |F u| ≤ g0/u^2 :=
    affine_tail_nonzero nodes m hlen hm hlast
  have htail' : ∀ u : ℝ, u ≠ 0 → |deriv F u| ≤ g1/u^2 := by
    intro u hu
    have h := Primal.deriv_inverseCosine_affineSpectrum_abs_le nodes m hlen hm hlast u hu
    convert h using 1 <;> dsimp [g1,nodalDerivativeTail] <;> field_simp <;> ring
  have hFi : Integrable F := integrable_inverseCosine_affineSpectrum nodes m hlen hm hlast
  have hlogi : Integrable (fun u : ℝ => |F u| *log |u|) :=
    integrable_signed_log_affine_inverse nodes m hlen hm hlast
  have hcap : ∀ u ∈ Icc (0:ℝ) (Δ*T0), |F u| ≤ nodalMassA0 nodes m := by
    intro u hu
    exact (inverseCosine_abs_le_mass _ (integrable_affineSpectrum nodes m hlen hm) u).trans
      (integral_abs_affineSpectrum_le nodes m hlen hm)
  have hmain : IntegrableOn (fun u : ℝ => log (u/d)*|F u|) (Ioi (Δ*T0)) :=
    (truncated_log_density_le F (inverseCosine_even _) hFi hlogi
      (∫ u : ℝ, |F u|) (nodalMassA0 nodes m) d (Δ*T0) le_rfl hd (by linarith) hr hr1 hcap).1
  have hmain' : IntegrableOn (fun u : ℝ => log (u/(2*π*Δ))/(2*π)*|F u|) (Ioi (Δ*T0)) := by
    apply (hmain.const_mul (1/(2*π))).congr
    filter_upwards with u
    have he : 2*π*Δ = d := by dsimp [Δ]; field_simp
    rw [he]
    ring
  have hrem := (affine_zero_remainder_integral_le nodes m hlen hm hlast Δ (Δ*T0) hΔ hΔ1 hr).1
  refine ⟨?_,continuous_deriv_inverseCosine_affineSpectrum nodes m hlen hm,
    inverseCosine_even _,⟨g0+g1,add_nonneg hg0 hg1,?_⟩,hmain',hrem,?_,?_⟩
  · intro u
    exact (hasDerivAt_inverseCosine_affineSpectrum nodes m hlen hm u).differentiableAt.hasDerivAt
  · intro u hu
    have hu0 : u ≠ 0 := by intro he; norm_num [he] at hu
    exact ⟨(htail u hu0).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_right hg1) (sq_nonneg u)),
      (htail' u hu0).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hg0) (sq_nonneg u))⟩
  · exact zero_main_boundary_tendsto F g0 Δ hg0 hΔ htail
  · exact zero_remainder_boundary_tendsto hcount F g0 Δ hg0 hΔ htail

#print axioms affine_CMSZeroAdmissible
end RH080Next.Explicit
