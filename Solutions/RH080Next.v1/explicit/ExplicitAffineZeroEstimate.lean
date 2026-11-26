/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineZeroAdmissible

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- Full actual zero contribution with the negative signed-log moment and
all derivative/truncation allowances. All affine admissibility fields are
proved, rather than supplied as a window-specific error estimate.
The remaining source input is the named GENERAL CMS summation-by-parts proof
scheme and general count/real-zeta propositions, explicitly recorded above. -/
theorem affine_zero_estimate (hsource : SourceCMSZeroPartialSummationProofScheme)
    (hcount : SourceCMSZeroCounting) (hRH : RiemannHypothesis)
    (hD : SourceDLMFRealEtaIntegral)
    (nodes : List ℚ) (m : ℕ) (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0)
    (d L T0 U : ℝ) (hd : 0 < d) (hd1 : d ≤ (1/10:ℝ))
    (hT0e : exp 1 ≤ T0) (hT010 : T0 < 10) (hQ : cmsQ T0 = 0)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) ≤ U) :
    Summable (realZeroFamily nodes m d L) ∧
    ‖(d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ)‖ ≤
      U*log (1/d)+nodalSignedLogUpper nodes m (3/8)+
      2*nodalMassA0 nodes m*((d/(2*π))*T0)*(1-log ((d/(2*π))*T0))+
      d*((3/10:ℝ)*nodalDerivativeTail nodes m+
        (3+(3/20:ℝ)*log (1/(d/(2*π))))*2*
          (nodalDerivativeCentral nodes m+nodalDerivativeTail nodes m)) := by
  let F := inverseCosine (affineSpectrum nodes m)
  let Δ := d/(2*π)
  let r := Δ*T0
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ1 : Δ ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2*π)).mpr
    linarith [Real.pi_gt_three]
  have hT0 : 0 < T0 := (exp_pos 1).trans_le hT0e
  have hr : 0 < r := mul_pos hΔ hT0
  have hr1 : r ≤ 1 := by
    have he : r*(2*π) = d*T0 := by dsimp [r,Δ]; field_simp <;> ring
    have hh : d*T0 ≤ 1 := by nlinarith
    nlinarith [Real.pi_gt_three]
  have hadm := affine_CMSZeroAdmissible hcount nodes m hlen hm hlast d T0 hd hd1 hT0e hT010
  obtain ⟨hsum,hzero⟩ := mellin_zero_norm_bound hsource hcount hRH hD nodes m d L T0 hd hT0e hT010 hQ hadm
  have hcap : ∀ u ∈ Icc (0:ℝ) r, |F u| ≤ nodalMassA0 nodes m := by
    intro u hu
    exact (inverseCosine_abs_le_mass _ (integrable_affineSpectrum nodes m hlen hm) u).trans
      (integral_abs_affineSpectrum_le nodes m hlen hm)
  obtain ⟨hmi,hmain⟩ := truncated_log_density_le F (inverseCosine_even _)
    (integrable_inverseCosine_affineSpectrum nodes m hlen hm hlast)
    (integrable_signed_log_affine_inverse nodes m hlen hm hlast)
    U (nodalMassA0 nodes m) d r hU hd (by linarith) hr hr1 hcap
  have hmainEq : 4*π*cmsZeroMain F Δ T0 = 2*(∫ u in Ioi r, log (u/d)*|F u|) := by
    unfold cmsZeroMain
    change 4*π*(∫ u in Ioi r, log (u/(2*π*Δ))/(2*π)*|F u|) = _
    rw [←integral_const_mul,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    have he : 2*π*Δ = d := by dsimp [Δ]; field_simp
    rw [he]
    field_simp <;> ring
  have hlog := signed_log_affine_inverse_three_eighths nodes m hlen hm hlast
  have hrem := affine_zero_remainder_normalized_le nodes m hlen hm hlast d r hd hΔ1 hr
  change ‖(d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ)‖ ≤
    4*π*cmsZeroMain F Δ T0+2*d*cmsZeroRemainder (deriv F) Δ T0 at hzero
  rw [hmainEq] at hzero
  dsimp only [cmsZeroRemainder] at hzero
  refine ⟨hsum,?_⟩
  change ‖(d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ)‖ ≤
    U*log (1/d)+nodalSignedLogUpper nodes m (3/8)+
      2*nodalMassA0 nodes m*r*(1-log r)+
      d*((3/10:ℝ)*nodalDerivativeTail nodes m+
        (3+(3/20:ℝ)*log (1/Δ))*2*
          (nodalDerivativeCentral nodes m+nodalDerivativeTail nodes m))
  dsimp only [F,Δ,r] at hmain hzero ⊢
  nlinarith

#print axioms affine_zero_estimate
end RH080Next.Explicit
