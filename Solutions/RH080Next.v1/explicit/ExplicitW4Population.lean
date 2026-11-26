/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitProfileApplications
import ExplicitActualPopulation
import WindowMaximum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.ExplicitProfiles
open RH080Next.Explicit

/-- The original recorded support-seven weighted-population coefficient line.
Only the analytic derivation is new; neither its input witness nor its claim
is replaced by the smaller new population programs. -/
def w4RecordedPopulationWidth (α : ℝ) : ℝ :=
  (851061745/1000000000:ℝ)+(1505657839/1000000000:ℝ)*α

private theorem w4_terminal : node w4Nodes (5*504)=0 := by
  rw [show 5*504=WindowPV.Data.nodes.length by rw [WindowPV.Data.nodes_length]]
  change node (WindowPV.Data.nodes++[0]) WindowPV.Data.nodes.length=0
  unfold node
  rw [List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self]
  norm_num

/-- The actual seventh C output is consumed by the mathematical sup bound.
The rounded decimal cap is a proved consequence of that source output. -/
theorem w4_source_amplitude_cap (v : ℝ) :
    |affineSpectrum w4Nodes 360 v|≤(69116963/100000000:ℝ) :=
  (WindowPV.source_first_window_bound v).trans (by norm_num)

/-- Full original weighted-population curve for every alpha≥0, proved via
actual support-seven Mellin/MV asymptotics and the ACTUAL IEANTN pi consumer.
Its FFT norm is explicitly still an argument. In particular no support-five
uniform-population theorem, fixed-window remainder or desired count bound
is introduced as an additional assumption. This is an eventual theorem;
no new finite onset is claimed. -/
theorem w4_recorded_population_of_norm
    (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|)≤w4OriginalNormCap)
    (α : ℝ) (hα : 0≤α) :
    IEANTN.CMSFunctional.GoodCoefficient α (w4RecordedPopulationWidth α) := by
  obtain ⟨hF,hA,hV0,hV1,hmu,hJ,hH,hW⟩ := w4_source_finite_caps
  let D := nodalF0 w4Nodes 360-4*IEANTN.CMSFunctional.positiveLeak (affineSpectrum w4Nodes 360)
  let c := w4RecordedPopulationWidth α
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
  exact actual_population_goodCoefficient hBR hCMS hDigamma hZero hCount hEta hMV hRH
    w4Nodes 360 504 (by norm_num) (by norm_num)
    (by rw [WindowPV.Data.affineNodes_length]) w4_terminal
    (by rw [WindowPV.Data.affineNodes_length]; norm_num)
    (by unfold radius; rw [WindowPV.Data.affineNodes_length]; norm_num)
    hA hV0 (hV1.trans (by norm_num)) (69116963/100000000) (19533921/25000000) c α
    (by norm_num) w4_source_amplitude_cap hNorm' hc hBase

#print axioms w4_source_amplitude_cap
#print axioms w4_recorded_population_of_norm
end RH080Next.ExplicitProfiles
