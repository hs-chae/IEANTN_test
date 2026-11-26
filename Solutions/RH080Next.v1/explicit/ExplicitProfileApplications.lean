/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitAnalyticTransfer
import ExplicitProfileResiduals
import FapInputBounds
import FapPositiveArea
import WindowInputBounds
import WindowPositiveArea

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.ExplicitProfiles
open RH080Next.Explicit

abbrev fapNodes := FapPV.Data.affineNodes
abbrev w4Nodes := WindowPV.Data.affineNodes

def fapOriginalNormCap : ℝ := (7817960157900848:ℝ)/10000000000000000

def w4OriginalNormCap : ℝ := (7813568381304104:ℝ)/10000000000000000

private theorem node_append_zero (xs : List ℚ) : node (xs++[0]) xs.length = 0 := by
  unfold node
  rw [List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self]
  norm_num

private theorem fap_last : node fapNodes 400 = 0 := by
  have h := node_append_zero FapPV.Data.nodes
  rw [FapPV.Data.nodes_length] at h
  exact h

private theorem w4_last : node w4Nodes 2520 = 0 := by
  have h := node_append_zero WindowPV.Data.nodes
  rw [WindowPV.Data.nodes_length] at h
  exact h

/-- Closed finite scalar/input facts about the ACTUAL original Fap witness.
The source-output facts consume the verified seven-output C program. A0 and
pointwise input bounds remain honestly identified as kernel input refinements. -/
theorem fap_source_finite_caps :
    (999999999/1000000000:ℝ) ≤ nodalF0 fapNodes 80 ∧
    nodalMassA0 fapNodes 80 ≤ 2 ∧ nodalV0 fapNodes ≤ 10 ∧
    nodalV1 fapNodes 80 ≤ (507714/125000:ℝ) ∧
    nodalMu2Upper fapNodes 80 ≤ (30963/125000:ℝ) ∧
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum fapNodes 80) ≤ (20371547/1000000000:ℝ) ∧
    nodalH fapNodes 80 ≤ (57139/500000:ℝ) ∧
    ∀ v : ℝ, |affineSpectrum fapNodes 80 v| ≤ 1 := by
  obtain ⟨hf,hH,hV,hmu⟩ := FapPV.source_first_nodal_boundaries
  refine ⟨?_,FapPV.input_mass_bound,?_,?_,?_,?_,?_,FapPV.input_window_bound⟩
  · rw [hf]; norm_num
  · rw [FapPV.source_first_variation]; norm_num
  · rw [hV]; norm_num
  · exact hmu.trans (by norm_num)
  · exact FapPV.source_first_positive_leak.trans (by norm_num)
  · rw [hH]; norm_num

/-- Closed finite facts about the DISTINCT original support-seven w4 data. -/
theorem w4_source_finite_caps :
    (999999999/1000000000:ℝ) ≤ nodalF0 w4Nodes 360 ∧
    nodalMassA0 w4Nodes 360 ≤ 2 ∧ nodalV0 w4Nodes ≤ 10 ∧
    nodalV1 w4Nodes 360 ≤ (509/125:ℝ) ∧
    nodalMu2Upper w4Nodes 360 ≤ (249/1000:ℝ) ∧
    IEANTN.CMSFunctional.positiveLeak (affineSpectrum w4Nodes 360) ≤ (2559477/125000000:ℝ) ∧
    nodalH w4Nodes 360 ≤ (14327/125000:ℝ) ∧
    ∀ v : ℝ, |affineSpectrum w4Nodes 360 v| ≤ 1 := by
  obtain ⟨hf,hH,hV,hmu⟩ := WindowPV.source_first_nodal_boundaries
  refine ⟨?_,WindowPV.input_mass_bound,?_,?_,?_,?_,?_,WindowPV.input_window_bound⟩
  · rw [hf]; norm_num
  · rw [WindowPV.source_first_variation]; norm_num
  · rw [hV]; norm_num
  · exact hmu.trans (by norm_num)
  · exact WindowPV.source_first_positive_leak.trans (by norm_num)
  · rw [hH]; norm_num

def FapSlabCase (c t : ℝ) : Prop :=
  (c = 4/5 ∧ t ∈ Icc (42:ℝ) 174) ∨
  (c = 37/50 ∧ t ∈ Icc (42:ℝ) 63) ∨
  (c = 3/4 ∧ t ∈ Icc (42:ℝ) 70)

section AnalyticInputs
variable (hBR : SourceBRFourierNormStrip) (hCMS : SourceCMSGuinandWeil)
    (hDigamma : SourceDLMFDigammaIntegral)
    (hZero : SourceCMSZeroPartialSummationProofScheme) (hCount : SourceCMSZeroCounting)
    (hEta : SourceDLMFRealEtaIntegral) (hMV : SourceMontgomeryVaughan) (hRH : RiemannHypothesis)
include hBR hCMS hDigamma hZero hCount hEta hMV hRH

/-- All locked Fap slab claims, with all scalar C outputs, analytic bridges,
actual arithmetic and strict endpoints consumed. ONLY the actual original
FFT norm fact remains an explicit numerical argument. This is deliberately
named `of_norm`; it is not claimed to close that unverified execution leaf. -/
theorem fap_strict_interval_of_norm
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ fapOriginalNormCap)
    (c t : ℝ) (hCase : FapSlabCase c t) :
    ∃ p : ℕ, Nat.Prime p ∧ exp t < (p:ℝ) ∧ (p:ℝ) < exp t+c*sqrt (exp t)*log (exp t) := by
  obtain ⟨hF,hA,hV0,hV1,hmu,hJ,hH,hW⟩ := fap_source_finite_caps
  have hdom : (1/2:ℝ) ≤ c ∧ c ≤ 4/5 ∧ 42 ≤ t := by
    rcases hCase with ⟨rfl,ht⟩ | ⟨rfl,ht⟩ | ⟨rfl,ht⟩
    · exact ⟨by norm_num,by norm_num,ht.1⟩
    · exact ⟨by norm_num,by norm_num,ht.1⟩
    · exact ⟨by norm_num,by norm_num,ht.1⟩
  have hS := fap_signed_cap fapNodes 80 hF hV1 hmu
  let J := IEANTN.CMSFunctional.positiveLeak (affineSpectrum fapNodes 80)
  let H := nodalH fapNodes 80
  let D := nodalF0 fapNodes 80-explicitPenalty*J
  let K := explicitConstant c J H (nodalSignedLogUpper fapNodes 80 (3/8)) 16
  have hJ0 : 0 ≤ J := by unfold J IEANTN.CMSFunctional.positiveLeak; apply integral_nonneg; intro v; exact le_max_left _ _
  have hH0 : 0 ≤ H := by unfold H nodalH; positivity
  have hK : K ≤ -(1939/2500:ℝ) := fap_constant_cap c J H _ (by linarith [hdom.1]) hdom.2.1 hJ0 hJ hH0 hH hS
  have hDcap : (574071/625000:ℝ) ≤ D := fap_denominator_lower _ _ hF hJ
  have hResidual : (1/1000000:ℝ) ≤ explicitResidual c D (3909/5000) K t := by
    rcases hCase with ⟨rfl,ht⟩ | ⟨rfl,ht⟩ | ⟨rfl,ht⟩
    · exact fap_08_residual D K t hDcap hK ht
    · exact fap_074_residual D K t hDcap hK ht
    · exact fap_075_residual D K t hDcap hK ht
  have hNorm' : (∫ u : ℝ, |inverseCosine (affineSpectrum fapNodes 80) u|) ≤ (3909/5000:ℝ) :=
    hNorm.trans (by norm_num [fapOriginalNormCap])
  apply actual_prime_interval_of_residual hBR hCMS hDigamma hZero hCount hEta hMV hRH
    fapNodes 80 80 (by norm_num) (by norm_num)
    (by rw [FapPV.Data.affineNodes_length] <;> norm_num) fap_last
    (by rw [FapPV.Data.affineNodes_length] <;> norm_num)
    (by unfold radius; rw [FapPV.Data.affineNodes_length] <;> norm_num) hA hV0
    (hV1.trans (by norm_num)) (hmu.trans (by norm_num))
    1 (by norm_num) (by norm_num) hW c t 16 (3909/5000) hdom.1 (by linarith [hdom.2.1]) hdom.2.2
    (by norm_num) (by norm_num) hNorm' (by norm_num)
    (by change 0 ≤ D; linarith) hResidual

/-- The entire original w4 analytic ray, with all actual source scalar and
support-seven applications closed; the original FFT norm is still explicit. -/
theorem w4_strict_ray_of_norm
    (hNorm : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|) ≤ w4OriginalNormCap)
    (t : ℝ) (ht : 42 ≤ t) :
    ∃ p : ℕ, Nat.Prime p ∧ exp t < (p:ℝ) ∧
      (p:ℝ) < exp t+(425531/500000:ℝ)*sqrt (exp t)*log (exp t) := by
  obtain ⟨hF,hA,hV0,hV1,hmu,hJ,hH,hW⟩ := w4_source_finite_caps
  have hS := w4_signed_cap w4Nodes 360 hF hV1 hmu
  let J := IEANTN.CMSFunctional.positiveLeak (affineSpectrum w4Nodes 360)
  let H := nodalH w4Nodes 360
  let D := nodalF0 w4Nodes 360-explicitPenalty*J
  let K := explicitConstant (425531/500000) J H (nodalSignedLogUpper w4Nodes 360 (3/8)) 1
  have hK : K ≤ 0 := w4_constant_cap _ J H _ hH hS
  have hDcap : (1836193/2000000:ℝ) ≤ D := w4_denominator_lower _ _ hF hJ
  have hResidual := w4_ray_residual D K t hDcap hK ht
  have hNorm' : (∫ u : ℝ, |inverseCosine (affineSpectrum w4Nodes 360) u|) ≤ (19533921/25000000:ℝ) :=
    hNorm.trans (by norm_num [w4OriginalNormCap])
  apply actual_prime_interval_of_residual hBR hCMS hDigamma hZero hCount hEta hMV hRH
    w4Nodes 360 504 (by norm_num) (by norm_num)
    (by rw [WindowPV.Data.affineNodes_length] <;> norm_num) w4_last
    (by rw [WindowPV.Data.affineNodes_length] <;> norm_num)
    (by unfold radius; rw [WindowPV.Data.affineNodes_length] <;> norm_num) hA hV0
    (hV1.trans (by norm_num)) (hmu.trans (by norm_num))
    1 (by norm_num) (by norm_num) hW (425531/500000) t 1 (19533921/25000000)
    (by norm_num) (by norm_num) ht (by norm_num) (by norm_num) hNorm' (by norm_num)
    (by change 0 ≤ D; linarith) hResidual

end AnalyticInputs
#print axioms fap_source_finite_caps
#print axioms w4_source_finite_caps
#print axioms fap_strict_interval_of_norm
#print axioms w4_strict_ray_of_norm
end RH080Next.ExplicitProfiles
