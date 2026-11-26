/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitSecondPoleIntegral

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def trivialYIntegrand (nodes : List ℚ) (m : ℕ) (d L y : ℝ) : ℝ :=
  mellinArithmeticWeight nodes m d L y/(y*(y^2-1))

private theorem gammaY_sub_secondPole (nodes : List ℚ) (m : ℕ) (d L y : ℝ) (hy : 1 < y) :
    gammaYIntegrand nodes m d L y-secondPoleYIntegrand nodes m d L y =
      trivialYIntegrand nodes m d L y := by
  have hy0 : y ≠ 0 := by linarith
  have hsq : y^2-1 ≠ 0 := by nlinarith
  have hs : sqrt y ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  have hden : 1-1/y^2 ≠ 0 := by
    have hy2 : 0 < y^2 := by positivity
    have hl : 1/y^2 < 1 := (div_lt_one hy2).mpr (by nlinarith)
    linarith
  unfold gammaYIntegrand secondPoleYIntegrand trivialYIntegrand mellinArithmeticWeight
  field_simp
  <;> ring

private theorem mellin_small_pole_value (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) :
    mellinTest H d L (-1/(2*Complex.I)) =
      ((d*exp (-L/2)*windowLaplaceIntegral nodes m (-d/2):ℝ):ℂ) := by
  have h := mellinTest_imaginary_value nodes m hlen hm H hH hreal d L (-1/2)
  have hz : -((-1/2:ℝ):ℂ)*Complex.I = -1/(2*Complex.I) := by
    push_cast
    field_simp
    norm_num [Complex.I_sq]
  rw [hz] at h
  simpa only [show L*(-1/2) = -L/2 by ring,show d*(-1/2) = -d/2 by ring] using h

/-- Full Gamma elimination and small-pole cancellation for the actual affine
source function, including finite support-seven substitution and integrability.
Only general CMS/DLMF source propositions are used by the preceding modules. -/
theorem mellin_gamma_small_pole_cancellation (hD : SourceDLMFDigammaIntegral)
    (nodes : List ℚ) (m : ℕ) (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L)
    (hformula : CMSGuinandWeilFormula (mellinTest H d L)) :
    IntervalIntegrable (trivialYIntegrand nodes m d L) volume
      (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d)) ∧
    mellinTest H d L (-1/(2*Complex.I))+
      (((1/(2*π):ℝ):ℂ))*(∫ r : ℝ, cmsGammaIntegrand (mellinTest H d L) r) =
        -(((∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d),
          trivialYIntegrand nodes m d L y):ℝ):ℂ) := by
  obtain ⟨hphi,hGamma⟩ := gamma_affine_frequency_integral hD nodes m hlen hm hlast H hH hreal d L hd hpositive hformula
  obtain ⟨hgy,hsub⟩ := gamma_positive_substitution nodes m hlen hm d L hd hpositive hphi
  obtain ⟨hty,htsub⟩ := second_pole_integral nodes m hlen hm d L hd
  have hR : 0 ≤ radius nodes m := by unfold radius; positivity
  have hY : exp (L-radius nodes m*d) ≤ exp (L+radius nodes m*d) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hY1 : 1 < exp (L-radius nodes m*d) := Real.one_lt_exp_iff.mpr (by linarith)
  have hpoint : EqOn (fun y : ℝ => gammaYIntegrand nodes m d L y-secondPoleYIntegrand nodes m d L y)
      (trivialYIntegrand nodes m d L)
      (uIcc (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d))) := by
    intro y hy
    rw [uIcc_of_le hY] at hy
    exact gammaY_sub_secondPole nodes m d L y (lt_of_lt_of_le hY1 hy.1)
  have htriv := (hgy.sub hty).congr (fun y hy => hpoint (uIoc_subset_uIcc hy))
  have htrivIntegral : (∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d),
      trivialYIntegrand nodes m d L y) =
      (∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d), gammaYIntegrand nodes m d L y)-
      (∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d), secondPoleYIntegrand nodes m d L y) := by
    rw [←intervalIntegral.integral_congr hpoint,intervalIntegral.integral_sub hgy hty]
  have hpole := mellin_small_pole_value nodes m hlen hm H hH hreal d L
  rw [←htsub] at hpole
  refine ⟨htriv,?_⟩
  rw [hpole,hGamma,hsub,htrivIntegral]
  push_cast
  ring

#print axioms mellin_gamma_small_pole_cancellation
end RH080Next.Explicit
