/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitRHMellin
import ExplicitPoleQuantitative
import ExplicitZeroAllowance
import ExplicitTrivialError
import ExplicitCMSZeroRoot

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

/-- A quantitative lower bound for the ACTUAL von-Mangoldt sum, composed from
all Fourier/strip/entire/Gamma/Mellin/zero-density/pole/trivial proofs.
The error 0.00011 is derived, not a premise. Prime powers and exterior primes
are subsequently removed by their separate arithmetic upper bounds. -/
theorem actual_mangoldt_lower_domain
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0)
    (hR : radius nodes m ≤ 10) (hA : nodalMassA0 nodes m ≤ 2)
    (hV0 : nodalV0 nodes ≤ 10) (hV1 : nodalV1 nodes m ≤ 50)
    (hMu : nodalMu2Upper nodes m ≤ 200)
    (c t T0 U : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hT0e : exp 1 ≤ T0) (hT010 : T0 < 10) (hQ : cmsQ T0 = 0)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) ≤ U) (hU2 : U ≤ 2) :
    Summable (weightedMangoldtFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t)) ∧
    poleScale c t*nodalF0 nodes m-U*(t/2-log (c*t/2))-
      nodalSignedLogUpper nodes m (3/8)-(11/100000:ℝ) <
      ∑' k : CMSPrimeIndex, weightedMangoldtFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t) k := by
  let d := halfLogWidth c t
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  have hpositive := mellin_positive_frequency_domain c t (radius nodes m) hc hc1 ht hR
  obtain ⟨hsum,hzeros,hEq⟩ := source_RH_affine_mellin_identity hBR hCMS hDigamma hRH
    nodes m n hm hmn hlen hlast d (t+d) hd hpositive
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hlen2 : 2 ≤ nodes.length := by rw [hlen]; omega
  have hlast' : node nodes (nodes.length-1) = 0 := by rw [hlen,Nat.add_sub_cancel]; exact hlast
  have hMu0 : 0 ≤ nodalMu2Upper nodes m :=
    (integral_nonneg (fun v : ℝ => mul_nonneg (sq_nonneg v) (abs_nonneg _))).trans
      (integral_sq_abs_affineSpectrum_le nodes m hlen2 hm hlast')
  have hpole := actual_mellin_pole_lower_domain nodes m hlen2 hm hlast' hR hMu0 hMu c t hc hc1 ht
  have hzero := (affine_zero_estimate_domain hZero hCount hRH hEta nodes m hlen2 hm hlast'
    hR hA hV0 hV1 c t T0 U hc hc1 ht hT0e hT010 hQ hU hU2).2
  have htriv := (trivial_integral_bound_domain nodes m hlen2 hm hR hA c t hc hc1 ht).2
  have hre := congrArg Complex.re hEq
  simp only [Complex.ofReal_re,Complex.sub_re] at hre
  have hRe := Complex.re_le_norm ((d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d (t+d) ρ))
  have hpEq : d*exp ((t+d)/2) = poleScale c t := by
    unfold poleScale
    rw [show (t+d)/2 = t/2+d/2 by ring]
  rw [hpEq] at hre
  have hTle := le_abs_self (∫ y in exp ((t+d)-radius nodes m*d)..exp ((t+d)+radius nodes m*d),
    trivialYIntegrand nodes m d (t+d) y)
  refine ⟨hsum,?_⟩
  change poleScale c t*nodalF0 nodes m-U*(t/2-log (c*t/2))-
    nodalSignedLogUpper nodes m (3/8)-(11/100000:ℝ) <
      ∑' k : CMSPrimeIndex, weightedMangoldtFamily nodes m d (t+d) k
  change ‖(d:ℂ)*(∑' ρ : CMSZeroIndex, realZeroFamily nodes m d (t+d) ρ)‖ < _ at hzero
  change |∫ y in exp ((t+d)-radius nodes m*d)..exp ((t+d)+radius nodes m*d),
    trivialYIntegrand nodes m d (t+d) y| < _ at htriv
  nlinarith

/-- The comparison-root existence is kernel-proved, so no root oracle or
additional source-root hypothesis appears in this public quantitative lower
bound. All source propositions are genuinely general analytic inputs. -/
theorem actual_mangoldt_lower
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m n : ℕ) (hm : 0 < m) (hmn : m ≤ n)
    (hlen : nodes.length = 5*n+1) (hlast : node nodes (5*n) = 0)
    (hR : radius nodes m ≤ 10) (hA : nodalMassA0 nodes m ≤ 2)
    (hV0 : nodalV0 nodes ≤ 10) (hV1 : nodalV1 nodes m ≤ 50)
    (hMu : nodalMu2Upper nodes m ≤ 200)
    (c t U : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|) ≤ U) (hU2 : U ≤ 2) :
    Summable (weightedMangoldtFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t)) ∧
    poleScale c t*nodalF0 nodes m-U*(t/2-log (c*t/2))-
      nodalSignedLogUpper nodes m (3/8)-(11/100000:ℝ) <
      ∑' k : CMSPrimeIndex, weightedMangoldtFamily nodes m (halfLogWidth c t) (t+halfLogWidth c t) k := by
  obtain ⟨T0,hT0e,hT09,hT010,hQ⟩ := cms_zero_count_root_exists
  exact actual_mangoldt_lower_domain hBR hCMS hDigamma hZero hCount hEta hRH
    nodes m n hm hmn hlen hlast hR hA hV0 hV1 hMu c t T0 U hc hc1 ht hT0e hT010 hQ hU hU2

#print axioms actual_mangoldt_lower
#print axioms actual_mangoldt_lower_domain
end RH080Next.Explicit
