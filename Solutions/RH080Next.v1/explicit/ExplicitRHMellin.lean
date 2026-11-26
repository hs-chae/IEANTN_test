/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMellinIdentity

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def realZeroFamily (nodes : List ℚ) (m : ℕ) (d L : ℝ) (ρ : CMSZeroIndex) : ℂ :=
  Complex.exp (Complex.I*(L:ℂ)*((ρ:ℂ).im:ℂ)) *
    (inverseCosine (affineSpectrum nodes m) ((d/(2*π))*(ρ:ℂ).im):ℂ) *
      ((IEANTN.zetaOrder (ρ:ℂ):ℤ):ℂ)

private theorem critical_zero_re (hRH : RiemannHypothesis) (ρ : CMSZeroIndex) :
    (ρ:ℂ).re = 1/2 := by
  apply hRH (ρ:ℂ) ρ.property.2.2
  · rintro ⟨n,heq⟩
    have he := congrArg Complex.re heq
    norm_num at he
    have hp := ρ.property.1.1
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · intro heq
    have he := congrArg Complex.re heq
    norm_num at he
    have hp := ρ.property.1.2
    linarith

private theorem critical_zero_argument (hRH : RiemannHypothesis) (ρ : CMSZeroIndex) :
    (((ρ:ℂ)-(1/2:ℂ))/Complex.I) = ((ρ:ℂ).im:ℂ) := by
  apply Complex.ext <;> simp [Complex.div_re,Complex.div_im,critical_zero_re hRH ρ]

private theorem cmsZeroFamily_eq_real (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m : ℕ) (H : ℂ → ℂ)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (ρ : CMSZeroIndex) :
    cmsZeroFamily (mellinTest H d L) ρ = (d:ℂ)*realZeroFamily nodes m d L ρ := by
  unfold cmsZeroFamily
  rw [critical_zero_argument hRH ρ]
  unfold mellinTest realZeroFamily
  have he : H (((d/(2*π):ℝ):ℂ)*((ρ:ℂ).im:ℂ)) =
      (inverseCosine (affineSpectrum nodes m) ((d/(2*π))*(ρ:ℂ).im):ℂ) := by
    rw [←Complex.ofReal_mul,hreal]
  rw [he]
  ring

/-- Fully composed Mellin identity on RH: actual weighted von-Mangoldt sum,
actual real Fourier amplitude at actual zero ordinates, and actual trivial
integral. No support-seven Mellin or Gamma identity is a premise. -/
theorem source_RH_affine_mellin_identity (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hD : SourceDLMFDigammaIntegral) (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0)
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L) :
    Summable (weightedMangoldtFamily nodes m d L) ∧ Summable (realZeroFamily nodes m d L) ∧
    (((∑' k : CMSPrimeIndex, weightedMangoldtFamily nodes m d L k):ℝ):ℂ) =
      ((d*exp (L/2)*windowLaplaceIntegral nodes m (d/2):ℝ):ℂ) -
      (d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ) -
      (((∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d),
        trivialYIntegrand nodes m d L y):ℝ):ℂ) := by
  obtain ⟨H,hH,hreal,hdec,hder⟩ := affine_strip_extension_by_mesh_dilation hBR nodes m n hm hmn hlen hlast
  obtain ⟨hk,hkdec⟩ := mellin_test_function_strip H hH hdec d L hd
  have hform : CMSGuinandWeilFormula (mellinTest H d L) := hCMS _ hk hkdec
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hlen2 : 2 ≤ nodes.length := by rw [hlen]; omega
  have hlast' : node nodes (nodes.length-1) = 0 := by rw [hlen,Nat.add_sub_cancel]; exact hlast
  obtain ⟨harith,htriv,hEq⟩ := affine_mellin_identity hD nodes m hlen2 hm hlast' H hH hreal d L hd hpositive hform
  have hdc : (d:ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsumZero : Summable (realZeroFamily nodes m d L) := by
    apply (hform.1.mul_left (d:ℂ)⁻¹).congr
    intro ρ
    rw [cmsZeroFamily_eq_real hRH nodes m H hreal d L ρ,←mul_assoc,inv_mul_cancel₀ hdc,one_mul]
  have hZeroEq : (∑' ρ : CMSZeroIndex, cmsZeroFamily (mellinTest H d L) ρ) =
      (d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d L ρ) := by
    simp_rw [cmsZeroFamily_eq_real hRH nodes m H hreal d L]
    rw [tsum_mul_left]
  rw [hZeroEq] at hEq
  exact ⟨harith,hsumZero,hEq⟩

#print axioms source_RH_affine_mellin_identity
end RH080Next.Explicit
