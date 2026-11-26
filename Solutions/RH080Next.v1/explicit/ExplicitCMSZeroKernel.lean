/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitCMSPositiveTransfer
import ExplicitCMSConjugation
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
namespace RH080Next.Explicit

/-- The former unformalized generic extension is now a kernel theorem. The
only counting input is the literal CMS Lemma9/right-closed count. Actual
ordinary FTC/Fubini, finite smoothing, infinite limits, and actual zeta-order
conjugation discharge every step; no source proof-scheme premise remains. -/
theorem cms_zero_partial_summation_kernel : SourceCMSZeroPartialSummationProofScheme:=by
  intro hcount hRH a ha hten hroot hzero F F' Δ hΔ hadm s hs
  obtain ⟨positive,bound⟩:=ZeroSummation.positive_transfer hcount a ha hzero hroot F F' Δ hΔ hadm
  rcases hs with rfl|rfl
  · exact ⟨positive,bound⟩
  · obtain ⟨negative,equal⟩:=CMSConjugation.negative_of_positive hadm.2.2.1 Δ positive
    exact ⟨negative,equal.trans_le bound⟩

/-- Full actual-zero bound with the formerly assumed source scheme replaced
by the preceding proved theorem. Other literal analytic source inputs remain
explicit, including real-axis nonvanishing's DLMF eta integral. -/
theorem cms_full_zero_bound_kernel (hcount : SourceCMSZeroCounting) (hRH : RiemannHypothesis)
    (hD : SourceDLMFRealEtaIntegral)
    (a : ℝ) (ha : exp 1≤ a) (hten : a<10) (hroot : cmsQ a=0)
    (F F' : ℝ → ℝ) (Δ : ℝ) (hΔ : 0<Δ) (hadm : CMSZeroAdmissible F F' Δ a) :
    Summable (cmsAmplitude F Δ) ∧
      (∑'ρ : CMSZeroIndex,cmsAmplitude F Δ ρ)≤2*cmsZeroMain F Δ a+2*Δ*cmsZeroRemainder F' Δ a:=
  cms_full_zero_bound_from_sources cms_zero_partial_summation_kernel hcount hRH hD a ha hten hroot F F' Δ hΔ hadm

#print axioms cms_zero_partial_summation_kernel
#print axioms cms_full_zero_bound_kernel
end RH080Next.Explicit
