/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAffineZeroEstimate
import ExplicitDomain
import ExplicitWindowErrors
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem exp_power_lower (k : ℕ) (hk : k ≠ 0) : (27/10:ℝ)^k < exp (k:ℝ) := by
  have he : (27/10:ℝ) < exp 1 := by linarith [exp_one_gt_d9]
  have h := pow_lt_pow_left₀ he (by norm_num : (0:ℝ) ≤ 27/10) hk
  simpa only [←exp_nat_mul,mul_one] using h

private theorem small_d_log_upper (d : ℝ) (hd : 0 < d) (hdu : d ≤ (1/50000000:ℝ)) :
    d*log (2*π/d) ≤ (1/2500000:ℝ) := by
  let d0 : ℝ := 1/50000000
  have hd0 : 0 < d0 := by dsimp [d0]; norm_num
  have he : exp 1 ≤ 2*π/d0 := by
    apply (le_div_iff₀ hd0).mpr
    have hp := pi_gt_three
    have he := exp_one_lt_three
    dsimp [d0]
    nlinarith
  have hratio : 2*π/d0 ≤ 2*π/d := by
    exact div_le_div_of_nonneg_left (by positivity) hd hdu
  have hanti := log_div_self_antitoneOn he (he.trans hratio) hratio
  have hmul := mul_le_mul_of_nonneg_left hanti (by positivity : 0 ≤ 2*π)
  have hid (x : ℝ) (hx : x ≠ 0) : (2*π)*(log (2*π/x)/(2*π/x)) = x*log (2*π/x) := by field_simp
  rw [hid d hd.ne',hid d0 hd0.ne'] at hmul
  have hexp : (400000000:ℝ) < exp 20 := by
    have h := exp_power_lower 20 (by norm_num)
    norm_num at h
    linarith
  have hl : log (2*π/d0) ≤ 20 := by
    apply (log_le_iff_le_exp (by positivity : 0 < 2*π/d0)).mpr
    have hp := pi_lt_four
    dsimp [d0]
    nlinarith
  have hll := mul_le_mul_of_nonneg_left hl hd0.le
  dsimp [d0] at hmul hll
  linarith

private theorem low_cut_upper (A r : ℝ) (hA : A ≤ 2) (hA0 : 0 ≤ A)
    (hr : 0 < r) (hru : r ≤ (1/30000000:ℝ)) :
    2*A*r*(1-log r) < (1/250000:ℝ) := by
  have he : (1/30000000:ℝ) ≤ exp (-1) := by
    rw [exp_neg]
    rw [←one_div]
    apply (le_div_iff₀ (exp_pos 1)).mpr
    have h := exp_one_lt_three
    linarith
  have hanti := mul_log_strictAntiOn.antitoneOn
    (show r ∈ Icc (0:ℝ) (exp (-1)) from ⟨hr.le,hru.trans he⟩)
    (show (1/30000000:ℝ) ∈ Icc (0:ℝ) (exp (-1)) from ⟨by norm_num,he⟩) hru
  have hexp : (30000000:ℝ) < exp 18 := by
    have h := exp_power_lower 18 (by norm_num)
    norm_num at h
    linarith
  have hl : log (30000000:ℝ) < 18 := (log_lt_iff_lt_exp (by norm_num)).mpr hexp
  have hlr : -(18:ℝ) < log (1/30000000:ℝ) := by
    rw [log_div one_ne_zero (by norm_num : (30000000:ℝ)≠0),log_one]
    linarith
  have hr1 : r < 1 := by linarith
  have hlog : 0 ≤ 1-log r := by linarith [log_nonpos hr.le hr1.le]
  have hh : r*(1-log r) < (19/30000000:ℝ) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hA (by positivity : 0 ≤ r*(1-log r))
  nlinarith

/-- Every zero-count derivative and low-log cutoff allowance is bounded on
the full admissible real domain, from finite coefficient quantities only.
No claimed 0.0012 total error or numerical zero-sum bound is a hypothesis. -/
theorem zero_allowance_lt (nodes : List ℚ) (m : ℕ)
    (hR : radius nodes m ≤ 10) (hA : nodalMassA0 nodes m ≤ 2)
    (hV0 : nodalV0 nodes ≤ 10) (hV1 : nodalV1 nodes m ≤ 50)
    (d T0 : ℝ) (hd : 0 < d) (hdu : d ≤ (1/50000000:ℝ))
    (hT0 : 0 < T0) (hT010 : T0 ≤ 10) :
    2*nodalMassA0 nodes m*((d/(2*π))*T0)*(1-log ((d/(2*π))*T0))+
      d*((3/10:ℝ)*nodalDerivativeTail nodes m+
        (3+(3/20:ℝ)*log (1/(d/(2*π))))*2*
          (nodalDerivativeCentral nodes m+nodalDerivativeTail nodes m)) < (1/10000:ℝ) := by
  let B := nodalDerivativeCentral nodes m
  let C := nodalDerivativeTail nodes m
  have hR0 : 0 ≤ radius nodes m := by unfold radius; positivity
  have hA0 : 0 ≤ nodalMassA0 nodes m := by unfold nodalMassA0; positivity
  have hV00 : 0 ≤ nodalV0 nodes := by unfold nodalV0; positivity
  have hV10 : 0 ≤ nodalV1 nodes m := by unfold nodalV1; positivity
  have hB0 : 0 ≤ B := nodalDerivativeCentral_nonneg nodes m
  have hC0 : 0 ≤ C := nodalDerivativeTail_nonneg nodes m
  have hB : B ≤ 160 := by
    dsimp [B,nodalDerivativeCentral]
    have h1 := mul_le_mul (mul_le_mul_of_nonneg_left (pi_lt_four.le) (by norm_num : (0:ℝ)≤2)) hR hR0 (by norm_num : (0:ℝ)≤2*4)
    have h2 := mul_le_mul h1 hA hA0 (by norm_num : (0:ℝ)≤2*4*10)
    norm_num at h2
    exact h2
  have hC : C ≤ (260/3:ℝ) := by
    have hmul := mul_le_mul hR hV1 hV10 (by norm_num : (0:ℝ)≤10)
    have heq : C*(2*π) = radius nodes m*nodalV1 nodes m+2*nodalV0 nodes := by
      dsimp [C,nodalDerivativeTail]
      field_simp
    nlinarith [pi_gt_three]
  have hr : 0 < (d/(2*π))*T0 := by positivity
  have hru : (d/(2*π))*T0 ≤ (1/30000000:ℝ) := by
    have hp := pi_gt_three
    have heq : ((d/(2*π))*T0)*(2*π) = d*T0 := by field_simp
    have hh := mul_le_mul hdu hT010 hT0.le (by norm_num : (0:ℝ)≤1/50000000)
    nlinarith
  have hlow := low_cut_upper (nodalMassA0 nodes m) _ hA hA0 hr hru
  have hlog := small_d_log_upper d hd hdu
  have hlog0 : 0 ≤ d*log (2*π/d) := by
    have hratio : 1 ≤ 2*π/d := by
      apply (le_div_iff₀ hd).mpr
      linarith [pi_gt_three]
    exact mul_nonneg hd.le (log_nonneg hratio)
  have hE1 : d*((3/10:ℝ)*C+6*(B+C)) ≤ (1506/50000000:ℝ) := by
    have hinner : (3/10:ℝ)*C+6*(B+C) ≤ 1506 := by linarith
    have hh := mul_le_mul hdu hinner (by positivity : 0 ≤ (3/10:ℝ)*C+6*(B+C)) (by norm_num : (0:ℝ)≤1/50000000)
    norm_num at hh
    linarith
  have hE2 : (3/10:ℝ)*(d*log (2*π/d))*(B+C) ≤ (1480/50000000:ℝ) := by
    have hh := mul_le_mul hlog (add_le_add hB hC) (add_nonneg hB0 hC0) (by norm_num : (0:ℝ)≤1/2500000)
    nlinarith
  have heq : d*((3/10:ℝ)*C+(3+(3/20:ℝ)*log (1/(d/(2*π))))*2*(B+C)) =
      d*((3/10:ℝ)*C+6*(B+C))+(3/10:ℝ)*(d*log (2*π/d))*(B+C) := by
    rw [show 1/(d/(2*π)) = 2*π/d by field_simp]
    ring
  change _+d*((3/10:ℝ)*C+(3+(3/20:ℝ)*log (1/(d/(2*π))))*2*(B+C)) < _
  rw [heq]
  linarith

/-- The actual Mellin zero term on the original continuous prime-interval
parameter domain, including the logarithmic height linearization. The
0.000102 allowance is derived from the previous actual integral proofs. -/
theorem affine_zero_estimate_domain
    (hsource : SourceCMSZeroPartialSummationProofScheme)
    (hcount : SourceCMSZeroCounting) (hRH : RiemannHypothesis)
    (hD : SourceDLMFRealEtaIntegral)
    (nodes : List ℚ) (m : ℕ) (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0)
    (hR : radius nodes m ≤ 10) (hA : nodalMassA0 nodes m ≤ 2)
    (hV0 : nodalV0 nodes ≤ 10) (hV1 : nodalV1 nodes m ≤ 50)
    (c t T0 U : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hT0e : exp 1 ≤ T0) (hT010 : T0 < 10) (hQ : cmsQ T0 = 0)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) ≤ U) (hU2 : U ≤ 2) :
    Summable (realZeroFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t)) ∧
    ‖((halfLogWidth c t:ℝ):ℂ)*
      (∑' ρ : CMSZeroIndex, realZeroFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t) ρ)‖ <
      U*(t/2-log (c*t/2))+nodalSignedLogUpper nodes m (3/8)+(51/500000:ℝ) := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hsmall : halfLogWidth c t ≤ (1/50000000:ℝ) := by linarith
  obtain ⟨hsum,hzero⟩ := affine_zero_estimate hsource hcount hRH hD nodes m hlen hm hlast
    (halfLogWidth c t) (t+halfLogWidth c t) T0 U hd.1 (by linarith) hT0e hT010 hQ hU
  have hallow := zero_allowance_lt nodes m hR hA hV0 hV1 (halfLogWidth c t) T0
    hd.1 hsmall ((exp_pos 1).trans_le hT0e) hT010.le
  have hlog := log_inverse_halfLogWidth_upper c t hc hc1 ht
  have hU0 : 0 ≤ U := (integral_nonneg (fun u : ℝ => abs_nonneg _)).trans hU
  have hmul := mul_le_mul_of_nonneg_left hlog hU0
  refine ⟨hsum,?_⟩
  nlinarith

#print axioms affine_zero_estimate_domain
#print axioms zero_allowance_lt
end RH080Next.Explicit
