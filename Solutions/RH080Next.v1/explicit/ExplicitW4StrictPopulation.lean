/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitW4Population
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.ExplicitProfiles
open RH080Next.Explicit

/-- The strict coefficient-infimum form of the recorded original claim.
A slightly smaller actual good coefficient is exhibited, rather than
silently replacing strict infimum comparison by membership at the endpoint.
The original independent-review norm remains an explicit argument. -/
theorem w4_recorded_population_inf_lt_of_norm
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|)≤w4OriginalNormCap)
    (α : ℝ) (hα : 0≤α) :
    sInf (IEANTN.CMSFunctional.goodCoefficients α)<w4RecordedPopulationWidth α := by
  obtain ⟨hF,hA,hV0,hV1,hmu,hJ,hH,hW⟩ := w4_source_finite_caps
  let D := nodalF0 w4Nodes 360-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum w4Nodes 360)
  let c := w4RecordedPopulationWidth α-(1/100000000:ℝ)
  have hD : (183619347/200000000:ℝ)≤D := by dsimp [D]; linarith
  have hc : 0<c := by dsimp [c,w4RecordedPopulationWidth]; nlinarith
  have hBase : α<(c*D-(19533921/25000000:ℝ))/(2*(69116963/100000000:ℝ)) := by
    apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*(69116963/100000000:ℝ))).mpr
    have hmul := mul_le_mul_of_nonneg_left hD hc.le
    have hmargin : α*(2*(69116963/100000000:ℝ))<c*(183619347/200000000:ℝ)-(19533921/25000000:ℝ) := by
      dsimp [c,w4RecordedPopulationWidth]
      nlinarith
    linarith
  have hNorm' : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|)≤(19533921/25000000:ℝ) :=
    hNorm.trans (by norm_num [w4OriginalNormCap])
  have hlast : node w4Nodes (5*504)=0 := by
    rw [show 5*504=WindowPV.Data.nodes.length by rw [WindowPV.Data.nodes_length]]
    change node (WindowPV.Data.nodes++[0]) WindowPV.Data.nodes.length=0
    unfold node
    rw [List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self]
    norm_num
  have hgood := actual_population_goodCoefficient hBR hCMS hDigamma hZero hCount hEta hMV hRH
    w4Nodes 360 504 (by norm_num) (by norm_num)
    (by rw [WindowPV.Data.affineNodes_length]) hlast
    (by rw [WindowPV.Data.affineNodes_length]; norm_num)
    (by unfold radius; rw [WindowPV.Data.affineNodes_length]; norm_num)
    hA hV0 (hV1.trans (by norm_num)) (69116963/100000000) (19533921/25000000) c α
    (by norm_num) w4_source_amplitude_cap hNorm' hc hBase
  have bounded : BddBelow (IEANTN.CMSFunctional.goodCoefficients α) :=
    ⟨0,fun _ h => h.1.le⟩
  exact (csInf_le bounded hgood).trans_lt (by dsimp [c]; linarith)

#print axioms w4_recorded_population_inf_lt_of_norm
end RH080Next.ExplicitProfiles
