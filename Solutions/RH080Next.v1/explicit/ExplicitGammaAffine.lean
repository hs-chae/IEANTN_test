/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitGammaFourier
import ExplicitMellinPoles

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080Next.Explicit

private theorem integrable_mellinTest_real (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (hlast : node nodes (nodes.length-1) = 0)
    (H : ℂ → ℂ) (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) : Integrable (fun r : ℝ => mellinTest H d L (r:ℂ)) := by
  have hΔ : d/(2*π) ≠ 0 := by positivity
  have hf := ((integrable_inverseCosine_affineSpectrum nodes m hlen hm hlast).ofReal.comp_mul_left' hΔ).const_mul (d:ℂ)
  have hi : Integrable (fun r : ℝ => (d:ℂ)*(inverseCosine (affineSpectrum nodes m) ((d/(2*π))*r):ℂ)*
      Complex.exp (Complex.I*(L:ℂ)*(r:ℂ))) := by
    apply hf.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with r
      rw [Complex.norm_exp]
      simp [Complex.mul_re,Complex.mul_im]
  apply hi.congr
  filter_upwards with r
  unfold mellinTest
  have hr : H (((d/(2*π):ℝ):ℂ)*(r:ℂ)) =
      (inverseCosine (affineSpectrum nodes m) ((d/(2*π))*r):ℂ) := by
    rw [←Complex.ofReal_mul,hreal]
  rw [hr]

def gammaWeight (nodes : List ℚ) (m : ℕ) (d L u : ℝ) : ℝ :=
  digammaKernel u*affineSpectrum nodes m ((u/2-L)/d)

/-- Actual affine-kernel Gamma elimination through the real positive-frequency
integral. Absolute Fubini, source test-function conditions and all frequency
cancellations are proved; no support-seven Gamma identity is assumed. -/
theorem gamma_affine_frequency_integral (hD : SourceDLMFDigammaIntegral)
    (nodes : List ℚ) (m : ℕ) (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L)
    (hformula : CMSGuinandWeilFormula (mellinTest H d L)) :
    IntegrableOn (gammaWeight nodes m d L) (Ioi (0:ℝ)) ∧
      (((1/(2*π):ℝ):ℂ))*(∫ r : ℝ, cmsGammaIntegrand (mellinTest H d L) r) =
        (-1/2:ℂ)*(((∫ u in Ioi (0:ℝ), gammaWeight nodes m d L u):ℝ):ℂ) := by
  let K : ℝ → ℂ := fun r => mellinTest H d L (r:ℂ)
  have hK : Continuous K := by have hc := hH.continuous; unfold K mellinTest; fun_prop
  have hKi := integrable_mellinTest_real nodes m hlen hm hlast H hreal d L hd
  have hKG : Integrable (fun r : ℝ => K r*(gammaReal r:ℂ)) := hformula.2.2.1
  have hzero : (∫ r : ℝ, K r) = 0 := by
    have h := fourier_mellinTest_zero nodes m hlen hm hlast H hreal d L hd hpositive
    rw [Real.fourier_real_eq_integral_exp_smul] at h
    simpa only [mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_smul] using h
  obtain ⟨hfreq,hGamma⟩ := gamma_fourier_elimination hD K hK hKi hKG hzero
  have hpoint (u : ℝ) (hu : 0 < u) : (digammaKernel u:ℂ)*
      (𝓕 K (u/(4*π))+𝓕 K (-u/(4*π))) = (2*π:ℝ) • (gammaWeight nodes m d L u:ℂ) := by
    have hp := fourier_mellin_extension nodes m hlen hm hlast H hreal d L hd (u/(4*π))
    have hn := fourier_mellin_extension nodes m hlen hm hlast H hreal d L hd (-u/(4*π))
    change 𝓕 K (u/(4*π)) = _ at hp
    change 𝓕 K (-u/(4*π)) = _ at hn
    have hargp : (2*π*(u/(4*π))-L)/d = (u/2-L)/d := by field_simp <;> ring
    have hargn : (2*π*(-u/(4*π))-L)/d = -((u/2+L)/d) := by field_simp <;> ring
    have hv : radius nodes m ≤ |(2*π*(-u/(4*π))-L)/d| := by
      rw [hargn,abs_neg]
      apply le_trans _ (le_abs_self _)
      apply (le_div_iff₀ hd).mpr
      linarith
    rw [affineSpectrum_eq_zero_of_radius_le nodes m hlen hm _ hv] at hn
    rw [hp,hn,hargp]
    simp only [Complex.ofReal_zero,smul_zero,add_zero,Complex.real_smul,gammaWeight]
    push_cast
    ring
  have hphic : IntegrableOn (fun u : ℝ => (gammaWeight nodes m d L u:ℂ)) (Ioi (0:ℝ)) := by
    apply (hfreq.const_mul (((1/(2*π):ℝ):ℂ))).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [hpoint u hu]
    simp only [Complex.real_smul]
    push_cast
    field_simp
  have hphir := (@RCLike.reCLM ℂ _).integrable_comp hphic
  change IntegrableOn (fun u : ℝ => (gammaWeight nodes m d L u:ℂ).re) (Ioi (0:ℝ)) at hphir
  simp only [Complex.ofReal_re] at hphir
  refine ⟨hphir,?_⟩
  have hIntegral : (∫ u in Ioi (0:ℝ), (digammaKernel u:ℂ)*
      (𝓕 K (u/(4*π))+𝓕 K (-u/(4*π)))) =
      ((2*π:ℝ):ℂ)*(((∫ u in Ioi (0:ℝ), gammaWeight nodes m d L u):ℝ):ℂ) := by
    calc
      _ = ∫ u in Ioi (0:ℝ), ((2*π:ℝ):ℂ)*(gammaWeight nodes m d L u:ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        simpa only [Complex.real_smul] using hpoint u hu
      _ = _ := by rw [integral_const_mul]; congr 1; exact integral_ofReal
  change (((1/(2*π):ℝ):ℂ))*(∫ r : ℝ, K r*(gammaReal r:ℂ)) = _
  rw [hGamma,hIntegral]
  push_cast
  field_simp

#print axioms gamma_affine_frequency_integral
end RH080Next.Explicit
