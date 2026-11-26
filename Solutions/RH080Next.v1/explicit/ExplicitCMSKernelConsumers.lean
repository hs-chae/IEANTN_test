/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroKernel
import ExplicitFullRangeApplications
import ExplicitW4StrictPopulation
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.ExplicitProfiles
open RH080Next.Explicit RH080Next.FiniteGap

section LiteralInputs
variable (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
include hBR hCMS hDigamma hCount hEta hMV hRH

/-- Original all-real Fap0.8 conclusion; the generic zero-summation premise is
actually discharged by the new kernel proof. The original norm remains explicit. -/
theorem fap_08_full_kernel_of_norm (hgap : HistoricalFiniteGap)
    (hNorm : (∫u : ℝ,|inverseCosine (affineSpectrum fapNodes 80) u|)≤ fapOriginalNormCap)
    (x : ℝ) (hx : 4≤ x) (hX : x≤ exp 174) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)< x+(4/5:ℝ)*sqrt x*log x:=
  fap_08_full_of_norm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hgap hNorm x hx hX

theorem fap_074_full_kernel_of_norm (hgap : HistoricalFiniteGap)
    (hNorm : (∫u : ℝ,|inverseCosine (affineSpectrum fapNodes 80) u|)≤ fapOriginalNormCap)
    (x : ℝ) (hx : 11≤ x) (hX : x≤ exp 63) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)< x+(37/50:ℝ)*sqrt x*log x:=
  fap_074_full_of_norm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hgap hNorm x hx hX

theorem fap_075_full_kernel_of_norm (hgap : HistoricalFiniteGap)
    (hNorm : (∫u : ℝ,|inverseCosine (affineSpectrum fapNodes 80) u|)≤ fapOriginalNormCap)
    (x : ℝ) (hx : 11≤ x) (hX : x≤ exp 70) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)< x+(3/4:ℝ)*sqrt x*log x:=
  fap_075_full_of_norm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hgap hNorm x hx hX

/-- Exact original global0.851062 bound; no generalized zero-scheme argument. -/
theorem w4_global_full_kernel_of_norm (hgap : HistoricalFiniteGap)
    (hNorm : (∫u : ℝ,|inverseCosine (affineSpectrum w4Nodes 360) u|)≤ w4OriginalNormCap)
    (x : ℝ) (hx : 4≤ x) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)< x+(425531/500000:ℝ)*sqrt x*log x:=
  w4_global_full_of_norm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hgap hNorm x hx

/-- Original support-seven weighted-population curve, for all alpha≥0;
its actual analytic transfer now consumes the kernel zero theorem. -/
theorem w4_recorded_population_kernel_of_norm
    (hNorm : (∫u : ℝ,|inverseCosine (affineSpectrum w4Nodes 360) u|)≤ w4OriginalNormCap)
    (α : ℝ) (hα : 0≤α) : IEANTN.CMSFunctional.GoodCoefficient α (w4RecordedPopulationWidth α):=
  w4_recorded_population_of_norm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hNorm α hα

theorem w4_recorded_population_inf_lt_kernel_of_norm
    (hNorm : (∫u : ℝ,|inverseCosine (affineSpectrum w4Nodes 360) u|)≤ w4OriginalNormCap)
    (α : ℝ) (hα : 0≤α) : sInf (IEANTN.CMSFunctional.goodCoefficients α)< w4RecordedPopulationWidth α:=
  w4_recorded_population_inf_lt_of_norm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hNorm α hα

end LiteralInputs
#print axioms fap_08_full_kernel_of_norm
#print axioms fap_074_full_kernel_of_norm
#print axioms fap_075_full_kernel_of_norm
#print axioms w4_global_full_kernel_of_norm
#print axioms w4_recorded_population_kernel_of_norm
#print axioms w4_recorded_population_inf_lt_kernel_of_norm
end RH080Next.ExplicitProfiles
