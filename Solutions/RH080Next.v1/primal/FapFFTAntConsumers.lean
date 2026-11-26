/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapFFTNorm
import ExplicitFullRangeApplications
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal.FapFFTKernel
open RH080Next.Explicit RH080Next.ExplicitProfiles RH080Next.FiniteGap

section AnalyticInputs
variable (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
include hBRNorm hBR hCMS hDigamma hZero hCount hEta hMV hRH

/-- Every original locked Fap logarithmic slab, with its former numerical norm
premise now discharged by the complete kernel-only FFT/quadrature chain. -/
theorem kernel_fap_strict_slab (c t : ℝ) (hCase : FapSlabCase c t) :
    ∃p : Nat, Nat.Prime p ∧ exp t < (p:ℝ) ∧
      (p:ℝ) < exp t+c*sqrt (exp t)*log (exp t) := by
  have hnorm : (∫u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap := by
    simpa only [fapNodes, fapOriginalNormCap] using kernel_actual_norm hBRNorm
  exact fap_strict_interval_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hnorm c t hCase

variable (hgap : HistoricalFiniteGap)
include hgap

/-- All real4<=x<=exp174, genuine strict prime endpoints and the original0.8
coefficient. FFT numerical verification is kernel-only, not source-first PV. -/
theorem kernel_fap_08_full (x : ℝ) (hx : 4≤x) (hX : x≤exp 174) :
    ∃p : Nat, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(4/5:ℝ)*sqrt x*log x := by
  have hnorm : (∫u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap := by
    simpa only [fapNodes, fapOriginalNormCap] using kernel_actual_norm hBRNorm
  exact fap_08_full_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hgap hnorm x hx hX

/-- All real11<=x<=exp63, retaining original0.74 and strict endpoints. -/
theorem kernel_fap_074_full (x : ℝ) (hx : 11≤x) (hX : x≤exp 63) :
    ∃p : Nat, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(37/50:ℝ)*sqrt x*log x := by
  have hnorm : (∫u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap := by
    simpa only [fapNodes, fapOriginalNormCap] using kernel_actual_norm hBRNorm
  exact fap_074_full_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hgap hnorm x hx hX

/-- All real11<=x<=exp70, retaining original0.75 and strict endpoints. -/
theorem kernel_fap_075_full (x : ℝ) (hx : 11≤x) (hX : x≤exp 70) :
    ∃p : Nat, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(3/4:ℝ)*sqrt x*log x := by
  have hnorm : (∫u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap := by
    simpa only [fapNodes, fapOriginalNormCap] using kernel_actual_norm hBRNorm
  exact fap_075_full_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hgap hnorm x hx hX

end AnalyticInputs
#print axioms kernel_fap_strict_slab
#print axioms kernel_fap_08_full
#print axioms kernel_fap_074_full
#print axioms kernel_fap_075_full
end RH080Next.Primal.FapFFTKernel
