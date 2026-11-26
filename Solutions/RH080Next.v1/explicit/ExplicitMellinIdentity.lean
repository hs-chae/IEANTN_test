/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitMellinGammaCancellation

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

def weightedMangoldtFamily (nodes : List ℚ) (m : ℕ) (d L : ℝ) (n : CMSPrimeIndex) : ℝ :=
  (ArithmeticFunction.vonMangoldt (n:ℕ):ℝ)*mellinArithmeticWeight nodes m d L (n:ℕ)

private theorem mellin_main_pole_value (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) :
    mellinTest H d L (1/(2*Complex.I)) =
      ((d*exp (L/2)*windowLaplaceIntegral nodes m (d/2):ℝ):ℂ) := by
  have h := mellinTest_imaginary_value nodes m hlen hm H hH hreal d L (1/2)
  have hz : -((1/2:ℝ):ℂ)*Complex.I = 1/(2*Complex.I) := by
    push_cast
    field_simp
    norm_num [Complex.I_sq]
  rw [hz] at h
  simpa only [show L*(1/2) = L/2 by ring,show d*(1/2) = d/2 by ring] using h

/-- Complete actual Mellin explicit identity, derived from general CMS6 and
DLMF16 through the proved Fourier/entire/pole/Gamma/arithmetic paths. The
spectral family is written in its general zeta-zero form; under RH its
arguments reduce to the real zero ordinates. -/
theorem affine_mellin_identity (hD : SourceDLMFDigammaIntegral)
    (nodes : List ℚ) (m : ℕ) (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hreal : ∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ))
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L)
    (hformula : CMSGuinandWeilFormula (mellinTest H d L)) :
    Summable (weightedMangoldtFamily nodes m d L) ∧
    IntervalIntegrable (trivialYIntegrand nodes m d L) volume
      (exp (L-radius nodes m*d)) (exp (L+radius nodes m*d)) ∧
    (((∑' n : CMSPrimeIndex, weightedMangoldtFamily nodes m d L n):ℝ):ℂ) =
      ((d*exp (L/2)*windowLaplaceIntegral nodes m (d/2):ℝ):ℂ) -
      (∑' ρ : CMSZeroIndex, cmsZeroFamily (mellinTest H d L) ρ) -
      (((∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d),
        trivialYIntegrand nodes m d L y):ℝ):ℂ) := by
  have hfamily (n : CMSPrimeIndex) : cmsPrimeFamily (mellinTest H d L) n =
      ((2*π:ℝ):ℂ)*(weightedMangoldtFamily nodes m d L n:ℂ) := by
    rw [cmsPrimeFamily_mellinTest nodes m hlen hm hlast H hreal d L hd hpositive n]
    unfold weightedMangoldtFamily
    push_cast
    ring
  have hcast : Summable (fun n : CMSPrimeIndex => (weightedMangoldtFamily nodes m d L n:ℂ)) := by
    apply (hformula.2.1.mul_left (((1/(2*π):ℝ):ℂ))).congr
    intro n
    rw [hfamily]
    push_cast
    field_simp
  have hsum : Summable (weightedMangoldtFamily nodes m d L) := (Complex.summable_ofReal).mp hcast
  have hPrimeSum : (∑' n : CMSPrimeIndex, cmsPrimeFamily (mellinTest H d L) n) =
      ((2*π:ℝ):ℂ)*(((∑' n : CMSPrimeIndex, weightedMangoldtFamily nodes m d L n):ℝ):ℂ) := by
    simp_rw [hfamily]
    rw [tsum_mul_left,←Complex.ofReal_tsum]
  have hPrimeCoeff : (((1/(2*π):ℝ):ℂ))*(∑' n : CMSPrimeIndex, cmsPrimeFamily (mellinTest H d L) n) =
      (((∑' n : CMSPrimeIndex, weightedMangoldtFamily nodes m d L n):ℝ):ℂ) := by
    rw [hPrimeSum]
    push_cast
    field_simp
  obtain ⟨htriv,hcancel⟩ := mellin_gamma_small_pole_cancellation hD nodes m hlen hm hlast
    H hH hreal d L hd hpositive hformula
  have hCMS := hformula.2.2.2
  have hzero := fourier_mellinTest_zero nodes m hlen hm hlast H hreal d L hd hpositive
  rw [hzero,mul_zero,sub_zero,hPrimeCoeff,mellin_main_pole_value nodes m hlen hm H hH hreal d L] at hCMS
  refine ⟨hsum,htriv,?_⟩
  linear_combination hCMS+hcancel

/-- Support-seven (and other wider-support) application obtained from the
literal published arbitrary support-five class, never from a window-specific
Mellin identity premise. All newly created analytic bridges are consumed. -/
theorem source_affine_mellin_identity (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hD : SourceDLMFDigammaIntegral)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0)
    (d L : ℝ) (hd : 0 < d) (hpositive : radius nodes m*d < L) :
    ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      (∀ u : ℝ, H (u:ℂ) = (inverseCosine (affineSpectrum nodes m) u:ℂ)) ∧
      Summable (weightedMangoldtFamily nodes m d L) ∧
      (((∑' k : CMSPrimeIndex, weightedMangoldtFamily nodes m d L k):ℝ):ℂ) =
        ((d*exp (L/2)*windowLaplaceIntegral nodes m (d/2):ℝ):ℂ) -
        (∑' ρ : CMSZeroIndex, cmsZeroFamily (mellinTest H d L) ρ) -
        (((∫ y in exp (L-radius nodes m*d)..exp (L+radius nodes m*d),
          trivialYIntegrand nodes m d L y):ℝ):ℂ) := by
  obtain ⟨H,hH,hreal,hdec,hder⟩ := affine_strip_extension_by_mesh_dilation
    hBR nodes m n hm hmn hlen hlast
  obtain ⟨hk,hkdec⟩ := mellin_test_function_strip H hH hdec d L hd
  have hform : CMSGuinandWeilFormula (mellinTest H d L) := hCMS _ hk hkdec
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hlen2 : 2 ≤ nodes.length := by rw [hlen]; omega
  have hlast' : node nodes (nodes.length-1) = 0 := by rw [hlen,Nat.add_sub_cancel]; exact hlast
  obtain ⟨hsum,htriv,hEq⟩ := affine_mellin_identity hD nodes m hlen2 hm hlast'
    H hH hreal d L hd hpositive hform
  exact ⟨H,hH,hreal,hsum,hEq⟩

#print axioms affine_mellin_identity
#print axioms source_affine_mellin_identity
end RH080Next.Explicit
