/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTW4MainNumerics
import FFTFapMainConsumers
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
namespace RH080Next.FFTPV.W4Main
open RH080Next.Explicit RH080Next.ExplicitProfiles RH080Next.FiniteGap

section LiteralInputs
variable (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
include hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH

theorem source_w4_global (hgap : HistoricalFiniteGap) (x : ℝ) (hx : 4≤x) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
      (p:ℝ)<x+(425531/500000:ℝ)*sqrt x*log x := by
  have norm : (∫u : ℝ,|inverseCosine (affineSpectrum w4Nodes 360) u|)≤w4OriginalNormCap := by
    simpa only [w4Nodes,w4OriginalNormCap] using source_first_actual_norm hBRNorm
  exact w4_global_full_kernel_of_norm hBR hCMS hDigamma hCount hEta hMV hRH hgap norm x hx

theorem source_w4_population (α : ℝ) (hα : 0≤α) :
    IEANTN.CMSFunctional.GoodCoefficient α (w4RecordedPopulationWidth α) := by
  have norm : (∫u : ℝ,|inverseCosine (affineSpectrum w4Nodes 360) u|)≤w4OriginalNormCap := by
    simpa only [w4Nodes,w4OriginalNormCap] using source_first_actual_norm hBRNorm
  exact w4_recorded_population_kernel_of_norm hBR hCMS hDigamma hCount hEta hMV hRH norm α hα

theorem source_w4_population_inf_lt (α : ℝ) (hα : 0≤α) :
    sInf (IEANTN.CMSFunctional.goodCoefficients α)<w4RecordedPopulationWidth α := by
  have norm : (∫u : ℝ,|inverseCosine (affineSpectrum w4Nodes 360) u|)≤w4OriginalNormCap := by
    simpa only [w4Nodes,w4OriginalNormCap] using source_first_actual_norm hBRNorm
  exact w4_recorded_population_inf_lt_kernel_of_norm hBR hCMS hDigamma hCount hEta hMV hRH norm α hα

/-- The exact same numerical facts with only the FFT source-execution layer
removed. Existing common scalar providers and analytic assumptions are retained. -/
theorem matched_kernel_fft_global (hgap : HistoricalFiniteGap) (x : ℝ) (hx : 4≤x) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧
      (p:ℝ)<x+(425531/500000:ℝ)*sqrt x*log x := by
  have norm : (∫u : ℝ,|inverseCosine (affineSpectrum w4Nodes 360) u|)≤w4OriginalNormCap := by
    simpa only [w4Nodes,w4OriginalNormCap] using W4DAG24.kernel_actual_norm hBRNorm
  exact w4_global_full_kernel_of_norm hBR hCMS hDigamma hCount hEta hMV hRH hgap norm x hx

/-- Exact original endpoint choices; the coefficient is selected at the actual
real input, not extrapolated from a finite set of sampled log values. -/
def bestWidth (x : ℝ) : ℝ :=
  if x<11 then 777/1000 else
  if x≤exp 63 then 37/50 else
  if x≤exp 70 then 3/4 else
  if x≤exp 174 then 4/5 else 425531/500000

theorem source_piecewise (hgap : HistoricalFiniteGap) (x : ℝ) (hx : 4≤x) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)<x+bestWidth x*sqrt x*log x := by
  by_cases small : x<11
  · simpa only [bestWidth,if_pos small] using direct_small_0777 x hx small
  have eleven : 11≤x := le_of_not_gt small
  by_cases h63 : x≤exp 63
  · simpa only [bestWidth,if_neg small,if_pos h63] using
      FapMain.source_fap_074_full hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap x eleven h63
  by_cases h70 : x≤exp 70
  · simpa only [bestWidth,if_neg small,if_neg h63,if_pos h70] using
      FapMain.source_fap_075_full hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap x eleven h70
  by_cases h174 : x≤exp 174
  · simpa only [bestWidth,if_neg small,if_neg h63,if_neg h70,if_pos h174] using
      FapMain.source_fap_08_full hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap x hx h174
  · simpa only [bestWidth,if_neg small,if_neg h63,if_neg h70,if_neg h174] using
      source_w4_global hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap x hx

end LiteralInputs
end RH080Next.FFTPV.W4Main
