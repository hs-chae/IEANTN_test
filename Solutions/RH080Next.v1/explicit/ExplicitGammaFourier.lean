/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitDigammaFubini

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080Next.Explicit

private theorem integrable_fourier_integrand (K : ℝ → ℂ) (hKi : Integrable K) (ξ : ℝ) :
    Integrable (fun r : ℝ => Complex.exp ((-2*π*r*ξ:ℝ)*Complex.I)*K r) := by
  apply hKi.bdd_mul (c := 1)
  · fun_prop
  · filter_upwards with r
    rw [Complex.norm_exp]
    simp [Complex.mul_re]

theorem fourier_cosine_average (K : ℝ → ℂ) (hKi : Integrable K) (ξ : ℝ) :
    𝓕 K ξ+𝓕 K (-ξ) = 2*(∫ r : ℝ, K r*(cos (2*π*ξ*r):ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul,Real.fourier_real_eq_integral_exp_smul]
  change (∫ r : ℝ, Complex.exp ((-2*π*r*ξ:ℝ)*Complex.I)*K r)+
    (∫ r : ℝ, Complex.exp ((-2*π*r*(-ξ):ℝ)*Complex.I)*K r) = _
  rw [←integral_add (integrable_fourier_integrand K hKi ξ) (integrable_fourier_integrand K hKi (-ξ)),
    ←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  rw [Complex.ofReal_cos,Complex.cos]
  have h1 : ((-2*π*r*(-ξ):ℝ):ℂ)*Complex.I = ((2*π*ξ*r:ℝ):ℂ)*Complex.I := by push_cast; ring
  have h2 : ((-2*π*r*ξ:ℝ):ℂ)*Complex.I = -((2*π*ξ*r:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [h1,h2]
  ring

private theorem integral_digamma_inner (K : ℝ → ℂ) (hKi : Integrable K)
    (hzero : (∫ r : ℝ, K r) = 0) (u : ℝ) :
    (∫ r : ℝ, digammaDoubleKernel K r u) =
      (-1/2:ℂ)*((digammaKernel u:ℝ):ℂ)*(𝓕 K (u/(4*π))+𝓕 K (-u/(4*π))) := by
  have hcos : Integrable (fun r : ℝ => K r*(cos (r*u/2):ℂ)) := by
    apply hKi.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with r
      simpa only [Complex.norm_real,Real.norm_eq_abs] using Real.abs_cos_le_one (r*u/2)
  have heq : (fun r : ℝ => digammaDoubleKernel K r u) =
      (fun r : ℝ => (digammaKernel u:ℂ)*(K r-K r*(cos (r*u/2):ℂ))) := by
    funext r
    unfold digammaDoubleKernel
    push_cast
    ring
  rw [heq,integral_const_mul,integral_sub hKi hcos,hzero,zero_sub]
  have hF := fourier_cosine_average K hKi (u/(4*π))
  have harg (r : ℝ) : 2*π*(u/(4*π))*r = r*u/2 := by field_simp <;> ring
  simp_rw [harg] at hF
  have hneg : -(u/(4*π)) = -u/(4*π) := by ring
  rw [hneg] at hF
  rw [hF]
  ring

/-- General Gamma-to-Fourier elimination with a proved absolute Fubini
interchange and explicit integrability of the resulting frequency integral. -/
theorem gamma_fourier_elimination (hD : SourceDLMFDigammaIntegral)
    (K : ℝ → ℂ) (hK : Continuous K) (hKi : Integrable K)
    (hKG : Integrable (fun r : ℝ => K r*(gammaReal r:ℂ)))
    (hzero : (∫ r : ℝ, K r) = 0) :
    IntegrableOn (fun u : ℝ => (digammaKernel u:ℂ)*
      (𝓕 K (u/(4*π))+𝓕 K (-u/(4*π)))) (Ioi (0:ℝ)) ∧
    (∫ r : ℝ, K r*(gammaReal r:ℂ)) =
      (-1/2:ℂ)*(∫ u in Ioi (0:ℝ), (digammaKernel u:ℂ)*
        (𝓕 K (u/(4*π))+𝓕 K (-u/(4*π)))) := by
  have hprod := integrable_digamma_double_kernel hD K hK hKi hKG
  have hfreq : IntegrableOn (fun u : ℝ => (digammaKernel u:ℂ)*
      (𝓕 K (u/(4*π))+𝓕 K (-u/(4*π)))) (Ioi (0:ℝ)) := by
    apply (hprod.integral_prod_right.const_mul (-2:ℂ)).congr
    filter_upwards with u
    rw [integral_digamma_inner K hKi hzero u]
    ring
  refine ⟨hfreq,?_⟩
  have hdifference : (∫ r : ℝ, K r*(digammaDifference r:ℂ)) =
      ∫ r : ℝ, K r*(gammaReal r:ℂ) := by
    have heq : (fun r : ℝ => K r*(digammaDifference r:ℂ)) =
      (fun r : ℝ => K r*(gammaReal r:ℂ)-((Complex.digamma (1/4:ℂ)).re:ℂ)*K r) := by
      funext r
      unfold digammaDifference gammaReal
      push_cast
      ring
    rw [heq,integral_sub hKG (hKi.const_mul _),integral_const_mul,hzero,mul_zero,sub_zero]
  rw [←hdifference,digamma_difference_fubini hD K hK hKi hKG]
  simp_rw [integral_digamma_inner K hKi hzero]
  rw [←integral_const_mul]
  congr 1
  funext u
  ring

#print axioms gamma_fourier_elimination
end RH080Next.Explicit
