/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFapMainNumerics
import ExplicitCMSKernelConsumers
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory
namespace RH080Next.FFTPV.FapMain
open RH080Next.Explicit RH080Next.ExplicitProfiles RH080Next.FiniteGap

section LiteralAnalyticInputs
variable (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis) (hgap : HistoricalFiniteGap)
include hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap

/-- Original all-real strict 0.8 interval through exp174. Its norm is obtained
from the complete actual C main execution, including its true printf event, and its generic zero-sum
transfer is a kernel theorem. Only the literal named analytic, historical and
RH inputs remain. -/
theorem source_fap_08_full (x : ℝ) (hx : 4≤x) (hX : x≤exp 174) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)<x+(4/5:ℝ)*sqrt x*log x := by
  have norm : (∫u : ℝ,|inverseCosine (affineSpectrum fapNodes 80) u|)≤fapOriginalNormCap := by
    simpa only [fapNodes,fapOriginalNormCap] using source_first_actual_norm hBRNorm
  exact fap_08_full_kernel_of_norm hBR hCMS hDigamma hCount hEta hMV hRH hgap norm x hx hX

theorem source_fap_074_full (x : ℝ) (hx : 11≤x) (hX : x≤exp 63) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)<x+(37/50:ℝ)*sqrt x*log x := by
  have norm : (∫u : ℝ,|inverseCosine (affineSpectrum fapNodes 80) u|)≤fapOriginalNormCap := by
    simpa only [fapNodes,fapOriginalNormCap] using source_first_actual_norm hBRNorm
  exact fap_074_full_kernel_of_norm hBR hCMS hDigamma hCount hEta hMV hRH hgap norm x hx hX

theorem source_fap_075_full (x : ℝ) (hx : 11≤x) (hX : x≤exp 70) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)<x+(3/4:ℝ)*sqrt x*log x := by
  have norm : (∫u : ℝ,|inverseCosine (affineSpectrum fapNodes 80) u|)≤fapOriginalNormCap := by
    simpa only [fapNodes,fapOriginalNormCap] using source_first_actual_norm hBRNorm
  exact fap_075_full_kernel_of_norm hBR hCMS hDigamma hCount hEta hMV hRH hgap norm x hx hX

end LiteralAnalyticInputs
#print axioms source_fap_08_full
#print axioms source_fap_074_full
#print axioms source_fap_075_full
end RH080Next.FFTPV.FapMain
