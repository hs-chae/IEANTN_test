/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAsymptoticCentral

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
namespace RH080Next.Explicit

theorem central_right_endpoint_positive (c t : ℝ) (hc : 0<c) (ht : 0<t) :
    exp (t+2*halfLogWidth c t)=exp t+c*sqrt (exp t)*log (exp t) := by
  have hz : 0 < intervalRatio c t := by unfold intervalRatio; positivity
  unfold halfLogWidth
  rw [show 2*(log (1+intervalRatio c t)/2)=log (1+intervalRatio c t) by ring,
    exp_add,exp_log (by linarith : 0<1+intervalRatio c t),log_exp,←exp_half]
  unfold intervalRatio
  have he : exp t*exp (-t/2)=exp (t/2) := by rw [←exp_add]; congr 1; ring
  calc
    _ = exp t+c*t*(exp t*exp (-t/2)) := by ring
    _ = _ := by rw [he]; ring

/-- Exact association to the actual IEANTN pi consumer and its half-open
endpoint convention. This is not an abstract unspecified counting function. -/
theorem normalized_population_exp (c t : ℝ) (hc : 0<c) (ht : 0<t) :
    IEANTN.CMSFunctional.normalizedPopulation c (exp t)=
      exp (-t/2)*((realPrimesIoc (exp t) (exp (t+2*halfLogWidth c t))).card:ℝ) := by
  have hd := (halfLogWidth_squeeze c t hc ht).1
  have hab : exp t≤exp (t+2*halfLogWidth c t) := exp_le_exp.mpr (by linarith)
  unfold IEANTN.CMSFunctional.normalizedPopulation IEANTN.CMSFunctional.halfOpenCount IEANTN.CMSFunctional.piReal
  rw [←central_right_endpoint_positive c t hc ht,←realPrimesIoc_card _ _ hab,←exp_half]
  rw [div_eq_mul_inv,show (exp (t/2))⁻¹=exp (-t/2) by rw [←exp_neg]; congr 1; ring]
  ring

/-- General actual support-radius population transfer, proved here from the
actual Mellin, zero-count, MV, prime-power and central-prime-count paths.
In particular it covers the original support-seven w4 witness without
asserting that the published support-five uniform proposition applies. -/
theorem actual_population_goodCoefficient
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (nodes : List ℚ) (m n : ℕ) (hm : 0<m) (hmn : m≤n)
    (hlen : nodes.length=5*n+1) (hlast : node nodes (5*n)=0)
    (hmN : m<nodes.length-1) (hR : radius nodes m≤10)
    (hA : nodalMassA0 nodes m≤2) (hV0 : nodalV0 nodes≤10) (hV1 : nodalV1 nodes m≤50)
    (M U c α : ℝ) (hM : 0<M) (hW : ∀ v : ℝ, |affineSpectrum nodes m v|≤M)
    (hU : (∫ u : ℝ, |inverseCosine (affineSpectrum nodes m) u|)≤U) (hc : 0<c)
    (hbase : α<(c*(nodalF0 nodes m-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))-U)/(2*M)) :
    IEANTN.CMSFunctional.GoodCoefficient α c := by
  let base := (c*(nodalF0 nodes m-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))-U)/(2*M)
  let δ := (base-α)/2
  have hδ : 0<δ := by dsimp [δ,base]; linarith
  have hThreshold : (α+δ)*M<
      (c*(nodalF0 nodes m-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))-U)/2 := by
    have he : base*M=(c*(nodalF0 nodes m-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum nodes m))-U)/2 := by
      dsimp [base]
      field_simp
      <;> ring
    have hmarg := mul_pos hδ hM
    dsimp [δ] at hmarg ⊢
    nlinarith
  have hAbove : ∀ᶠ t : ℝ in atTop, (α+δ)*M<asymptoticNormalizedLower nodes m M U c t :=
    (tendsto_order.1 (asymptoticNormalizedLower_tendsto nodes m M U c hc)).1 _ hThreshold
  have hActual := eventual_actual_central_normalized_lower hBR hCMS hDigamma hZero hCount hEta hMV hRH
    nodes m n hm hmn hlen hlast hmN hR hA hV0 hV1 M U c hM.le hW hU hc
  have hPop : ∀ᶠ t : ℝ in atTop, α+δ≤IEANTN.CMSFunctional.normalizedPopulation c (exp t) := by
    filter_upwards [hAbove,hActual,eventually_ge_atTop (42:ℝ)] with t ht hlow ht42
    have ht0 : 0<t := by linarith
    have hd := (halfLogWidth_squeeze c t hc ht0).1
    have hCnt := centralPrimeSum_le_count nodes m (halfLogWidth c t) t M (by linarith) hd.le hM.le hW
    have hCnt' : centralPrimeSum nodes m (halfLogWidth c t) t/t≤
        M*exp (-t/2)*((realPrimesIoc (exp t) (exp (t+2*halfLogWidth c t))).card:ℝ) := by
      apply (div_le_iff₀ ht0).mpr
      calc
        _ ≤ M*t*exp (-t/2)*((realPrimesIoc (exp t) (exp (t+2*halfLogWidth c t))).card:ℝ) := hCnt
        _ = _ := by ring
    rw [normalized_population_exp c t hc ht0]
    have hStrict := ht.trans_le (hlow.trans hCnt')
    nlinarith
  refine ⟨hc,δ,hδ,?_⟩
  filter_upwards [tendsto_log_atTop.eventually hPop,eventually_gt_atTop (1:ℝ)] with x hx hx1
  simpa only [exp_log (by linarith : 0<x)] using hx

#print axioms central_right_endpoint_positive
#print axioms normalized_population_exp
#print axioms actual_population_goodCoefficient
end RH080Next.Explicit
