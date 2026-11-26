/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSZeroKernel
import FapFFTAntConsumers
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Primal.FapFFTKernel
open RH080Next.Explicit RH080Next.FiniteGap

section LiteralInputs
variable (hBRNorm : SourceBRFourierNormFive) (hBR : SourceBRFourierNormStrip)
    (hCMS : SourceCMSGuinandWeil) (hDigamma : SourceDLMFDigammaIntegral)
    (hCount : SourceCMSZeroCounting) (hEta : SourceDLMFRealEtaIntegral)
    (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis) (hgap : HistoricalFiniteGap)
include hBRNorm hBR hCMS hDigamma hCount hEta hMV hRH hgap

/-- Original all-real4..exp174 Fap0.8, with BOTH the numerical norm argument
and the generalized zero-scheme argument discharged. FFT is kernel-only;
source-first C FFT/main/ANT consumption is a separate proof boundary. -/
theorem kernel_fap_08_full_without_zero_scheme (x : ℝ) (hx : 4≤ x) (hX : x≤ exp 174) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)< x+(4/5:ℝ)*sqrt x*log x:=
  kernel_fap_08_full hBRNorm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hgap x hx hX

theorem kernel_fap_074_full_without_zero_scheme (x : ℝ) (hx : 11≤ x) (hX : x≤ exp 63) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)< x+(37/50:ℝ)*sqrt x*log x:=
  kernel_fap_074_full hBRNorm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hgap x hx hX

theorem kernel_fap_075_full_without_zero_scheme (x : ℝ) (hx : 11≤ x) (hX : x≤ exp 70) :
    ∃p : ℕ,Nat.Prime p ∧ x<(p:ℝ) ∧ (p:ℝ)< x+(3/4:ℝ)*sqrt x*log x:=
  kernel_fap_075_full hBRNorm hBR hCMS hDigamma cms_zero_partial_summation_kernel hCount hEta hMV hRH hgap x hx hX
end LiteralInputs
#print axioms kernel_fap_08_full_without_zero_scheme
#print axioms kernel_fap_074_full_without_zero_scheme
#print axioms kernel_fap_075_full_without_zero_scheme
end RH080Next.Primal.FapFFTKernel
