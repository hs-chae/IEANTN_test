/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ActualArithmeticSplit
import ExplicitMellinLower
import ExplicitErrorBudget

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- Complete analytic and arithmetic transfer to the ACTUAL central prime
sum. Every new Fourier/Mellin/zero/MV/BV/power/budget lemma is consumed.
The numerical norm bound is an explicit provider argument, so this theorem
does not pretend to complete an unverified FFT execution leaf. -/
theorem actual_central_residual_lower
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0)
    (hmN : m < nodes.length-1)
    (hR : radius nodes m ≤ 10) (hA : nodalMassA0 nodes m ≤ 2)
    (hV0 : nodalV0 nodes ≤ 10) (hV1 : nodalV1 nodes m ≤ 50)
    (hMu : nodalMu2Upper nodes m ≤ 200)
    (M : ℝ) (hM0 : 0 ≤ M) (hM2 : M ≤ 2)
    (hW : ∀ v : ℝ, |affineSpectrum nodes m v| ≤ M)
    (c t k U : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) ≤ U) (hU2 : U ≤ 2)
    (hD : 0 ≤ nodalF0 nodes m-explicitPenalty*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)) :
    explicitResidual c
      (nodalF0 nodes m-explicitPenalty*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)) U
      (explicitConstant c (IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))
        (nodalH nodes m) (nodalSignedLogUpper nodes m (3/8)) k) t <
      centralPrimeSum nodes m (halfLogWidth c t) t := by
  let d := halfLogWidth c t
  let L := t+d
  let J := IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)
  let H := nodalH nodes m
  let A := ∑' p : CMSPrimeIndex, weightedMangoldtFamily nodes m d L p
  let powers := ∑' p : CMSPrimeIndex, Primal.actualNonprimeMangoldtFamily nodes m d L p
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hlen2 : 2 ≤ nodes.length := by rw [hlen]; omega
  have hlast' : node nodes (nodes.length-1) = 0 := by rw [hlen,Nat.add_sub_cancel]; exact hlast
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  have hR0 : 0 ≤ radius nodes m := by unfold radius; positivity
  have hpositive := mellin_positive_frequency_domain c t (radius nodes m) hc hc1 ht hR
  have hell := (mv_block_parameters c t k hc hc1 ht hk hk16).1
  have hMellin := (actual_mangoldt_lower hBR hCMS hDigamma hZero hCount hEta hRH
    nodes m n hm hmn hlen hlast hR hA hV0 hV1 hMu c t U hc hc1 ht hU hU2).2
  have hArithmetic := (Primal.actual_full_arithmetic_wing_bound hMV nodes m hlen2 hm hmN hlast'
    d L (mvBlockLength c t k) hd hpositive hell).2
  have hPower := (Primal.actual_nonprimeMangoldt_lt nodes m hlen2 hm c t M hc hc1 ht hR hM0 hM2 hW).2
  have hJ0 : 0 ≤ J := by
    unfold J IEANTN.CMSFunctional.positiveLeak
    apply integral_nonneg
    intro v
    exact le_max_left _ _
  have hH0 : 0 ≤ H := by dsimp [H,nodalH]; positivity
  have hMVlin := mv_wing_allowance_linearized c t (radius nodes m) k J H hc hc1 ht hR0 hR hk hk16 hJ0 hH0
  have hCentral : Primal.centralPrimePart nodes m d L = centralPrimeSum nodes m d t := by
    unfold Primal.centralPrimePart centralPrimeSum
    dsimp [L]
    rw [show t+d-d = t by ring,show t+d+d = t+2*d by ring]
  rw [hCentral] at hArithmetic
  have hUpper : A ≤ centralPrimeSum nodes m d t+explicitPenalty*poleScale c t*J+
      explicitPenalty*J*c*log k/mvBlockDenom k 42+2*explicitPenalty*H/(k*mvBlockDenom k 42)+powers := by
    change A ≤ centralPrimeSum nodes m d t+_+_+powers at hArithmetic
    change _ ≤ explicitPenalty*poleScale c t*J+
      explicitPenalty*J*c*log k/mvBlockDenom k 42+2*explicitPenalty*H/(k*mvBlockDenom k 42) at hMVlin
    linarith
  have hF02 : nodalF0 nodes m ≤ 2 := by
    rw [←integral_affineSpectrum nodes m hm]
    exact (integral_mono (integrable_affineSpectrum nodes m hlen2 hm)
      (integrable_affineSpectrum nodes m hlen2 hm).abs (fun v => le_abs_self _)).trans
      ((integral_abs_affineSpectrum_le nodes m hlen2 hm).trans hA)
  have hD2 : nodalF0 nodes m-explicitPenalty*J ≤ 2 := by
    have hh : 0 ≤ explicitPenalty*J := by unfold explicitPenalty; positivity
    linarith
  exact explicit_budget_assembly c t (nodalF0 nodes m) J H U
    (nodalSignedLogUpper nodes m (3/8)) k (poleScale c t) A
    (centralPrimeSum nodes m d t) powers hD hD2
    (poleScale_lower c t hc hc1 ht) hMellin hUpper hPower

/-- Full genuine prime-interval consumer of the preceding quantitative
transfer and scalar residual. Both interval endpoints are strict. -/
theorem actual_prime_interval_of_residual
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0)
    (hmN : m < nodes.length-1)
    (hR : radius nodes m ≤ 10) (hA : nodalMassA0 nodes m ≤ 2)
    (hV0 : nodalV0 nodes ≤ 10) (hV1 : nodalV1 nodes m ≤ 50)
    (hMu : nodalMu2Upper nodes m ≤ 200)
    (M : ℝ) (hM0 : 0 ≤ M) (hM2 : M ≤ 2)
    (hW : ∀ v : ℝ, |affineSpectrum nodes m v| ≤ M)
    (c t k U : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) ≤ U) (hU2 : U ≤ 2)
    (hD : 0 ≤ nodalF0 nodes m-explicitPenalty*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))
    (hResidual : (1/1000000:ℝ) ≤ explicitResidual c
      (nodalF0 nodes m-explicitPenalty*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m)) U
      (explicitConstant c (IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))
        (nodalH nodes m) (nodalSignedLogUpper nodes m (3/8)) k) t) :
    ∃ p : ℕ, Nat.Prime p ∧ exp t < (p:ℝ) ∧
      (p:ℝ) < exp t+c*sqrt (exp t)*log (exp t) := by
  have hLower := actual_central_residual_lower hBR hCMS hDigamma hZero hCount hEta hMV hRH
    nodes m n hm hmn hlen hlast hmN hR hA hV0 hV1 hMu M hM0 hM2 hW c t k U hc hc1 ht hk hk16 hU hU2 hD
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  obtain ⟨p,hp,hlo,hhi⟩ := strict_prime_of_central_lower nodes m (halfLogWidth c t) t M _
    ht hd.le hM0 hM2 hW hResidual hLower.le
  rw [central_right_endpoint c t hc ht] at hhi
  exact ⟨p,hp,hlo,hhi⟩

#print axioms actual_central_residual_lower
#print axioms actual_prime_interval_of_residual
end RH080Next.Explicit
