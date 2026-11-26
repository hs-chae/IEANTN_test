/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitProfileApplications
import FinitePrimeGapBridge

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.ExplicitProfiles
open RH080Next.Explicit RH080Next.FiniteGap

private theorem widen_prime_interval (x a b : ℝ) (hx : 1 ≤ x) (hab : a ≤ b)
    (h : ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+a*sqrt x*log x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+b*sqrt x*log x := by
  obtain ⟨p,hp,hlo,hhi⟩ := h
  refine ⟨p,hp,hlo,hhi.trans_le ?_⟩
  gcongr
  exact log_nonneg hx

private theorem log_slab_of_large (x T : ℝ) (hx : exp 42 ≤ x) (hX : x ≤ exp T) :
    log x ∈ Icc (42:ℝ) T := by
  have hpos : 0 < x := (exp_pos 42).trans_le hx
  constructor
  · apply exp_le_exp.mp
    rwa [exp_log hpos]
  · apply exp_le_exp.mp
    rwa [exp_log hpos]

section AnalyticInputs
variable (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (hgap : HistoricalFiniteGap)
include hBR hCMS hDigamma hZero hCount hEta hMV hRH hgap

/-- Complete all-real original Fap 0.8 interval, including the finite range.
The actual original Fap Fourier norm remains explicitly unverified here. -/
theorem fap_08_full_of_norm
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap)
    (x : ℝ) (hx : 4 ≤ x) (hX : x ≤ exp 174) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(4/5:ℝ)*sqrt x*log x := by
  by_cases hs : x ≤ exp 42
  · simpa only [show (8/10:ℝ) = 4/5 by norm_num] using finite_open_08_through_exp42 hgap x hx hs
  have hpos : 0 < x := by linarith
  have hl := log_slab_of_large x 174 (le_of_not_ge hs) hX
  simpa only [exp_log hpos] using
    fap_strict_interval_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hNorm
      (4/5) (log x) (Or.inl ⟨rfl,hl⟩)

/-- Complete all-real original Fap 0.74 interval starting at eleven. -/
theorem fap_074_full_of_norm
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap)
    (x : ℝ) (hx : 11 ≤ x) (hX : x ≤ exp 63) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(37/50:ℝ)*sqrt x*log x := by
  by_cases hs : x ≤ exp 42
  · simpa only [show (74/100:ℝ) = 37/50 by norm_num] using historical_gap_implies_074 hgap x hx (hs.trans exp42_lt_historical_cutoff.le)
  have hpos : 0 < x := by linarith
  have hl := log_slab_of_large x 63 (le_of_not_ge hs) hX
  simpa only [exp_log hpos] using
    fap_strict_interval_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hNorm
      (37/50) (log x) (Or.inr (Or.inl ⟨rfl,hl⟩))

/-- Complete all-real original Fap 0.75 interval starting at eleven. -/
theorem fap_075_full_of_norm
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap)
    (x : ℝ) (hx : 11 ≤ x) (hX : x ≤ exp 70) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧ (p:ℝ) < x+(3/4:ℝ)*sqrt x*log x := by
  by_cases hs : x ≤ exp 42
  · exact widen_prime_interval x (74/100) (3/4) (by linarith) (by norm_num)
      (historical_gap_implies_074 hgap x hx (hs.trans exp42_lt_historical_cutoff.le))
  have hpos : 0 < x := by linarith
  have hl := log_slab_of_large x 70 (le_of_not_ge hs) hX
  simpa only [exp_log hpos] using
    fap_strict_interval_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hNorm
      (3/4) (log x) (Or.inr (Or.inr ⟨rfl,hl⟩))

/-- Complete original support-seven w4 bound for every real x at least four.
The final theorem consumes the finite source computation and every new
analytic/source-scalar bridge; only its actual original FFT norm is a numerical
argument. No native execution or desired final-bound premise is hidden. -/
theorem w4_global_full_of_norm
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|) ≤ w4OriginalNormCap)
    (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p:ℝ) ∧
      (p:ℝ) < x+(425531/500000:ℝ)*sqrt x*log x := by
  by_cases hs : x ≤ exp 42
  · exact widen_prime_interval x (8/10) (425531/500000) (by linarith) (by norm_num)
      (finite_open_08_through_exp42 hgap x hx hs)
  have hpos : 0 < x := by linarith
  have hl : 42 ≤ log x := (log_slab_of_large x (log x) (le_of_not_ge hs)
    (by rw [exp_log hpos])).1
  simpa only [exp_log hpos] using
    w4_strict_ray_of_norm hBR hCMS hDigamma hZero hCount hEta hMV hRH hNorm (log x) hl

end AnalyticInputs
#print axioms fap_08_full_of_norm
#print axioms fap_074_full_of_norm
#print axioms fap_075_full_of_norm
#print axioms w4_global_full_of_norm
end RH080Next.ExplicitProfiles
