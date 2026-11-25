/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CompactDualSourceFirst
import IEANTN.Nodes.CMSDualCertificate.v1.Conclusions
import IEANTN.Nodes.CMSFunctionalObstruction.v1.Conclusions

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
open scoped FourierTransform
namespace RH080.Dual

lemma compactStep_even : Function.Even compactStep := by
  intro x
  simp [compactStep, stepCell, box_eq, abs_neg]

/-- The computation's complete source package remains paired with its abstract
mathematical witness; core node declarations expose only Mathlib propositions. -/
theorem source_integral_witness_with_source :
    RH080PV.Verified.SourceFirstOutput ∧ CMSDualCertificate.v1.integral_witness := by
  have joint := actual_source_first_functional_result
  refine ⟨joint.1, ?_⟩
  refine ⟨compactStep, compactStep_integrable, compactStep_even,
    compactStep_center, ?_, ?_⟩
  · intro t _
    exact compactStep_bounds t
  · intro x
    exact joint.2.1 x

/-- Reusable mathematical pipeline: consume the witness actually supplied by
the caller, rather than reconstructing a closed twenty-step numerical fact. -/
theorem integralWitness_ratio_floor (A M : ℝ) (hA : 1 ≤ A) (hM : 0 < M)
    (witness : IEANTN.CMSDual.IntegralWitness A M) :
    IEANTN.CMSDual.L1RatioFloor A (1/M) := by
  obtain ⟨V,hV,_heven,hcenter,hrange,hkernel⟩ := witness
  intro F G hF hG hcont hfourier hden
  change 0 < F 0-A*(∫ t in exterior, max 0 (G t)) at hden
  have hweak := weak_duality_l1 F G V A M hF hG hV hcont hfourier hA
    (fun t ht => hcenter t (le_of_not_gt ht))
    (fun t ht => (hrange t ht).1) (fun t ht => (hrange t ht).2) hkernel
  have hmass : 0 < (∫ x : ℝ, |F x|) := by
    by_contra h
    have hn : M*(∫ x : ℝ, |F x|) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hM.le (le_of_not_gt h)
    linarith
  exact RH080.Functional.ratio_lower_of_dual hmass hden hM hweak

end RH080.Dual

namespace CMSDualCertificate.v1

theorem challenge_integral_witness : integral_witness :=
  RH080.Dual.source_integral_witness_with_source.2

end CMSDualCertificate.v1

namespace CMSFunctionalObstruction.v1

theorem challenge_ratio_floor (witness : CMSDualCertificate.v1.integral_witness) :
    ratio_floor := by
  have h := RH080.Dual.integralWitness_ratio_floor (36/11) (123/100)
    (by norm_num) (by norm_num) witness
  have hc : (1/(123/100) : ℝ) = 100/123 := by norm_num
  rw [hc] at h
  exact h

theorem challenge_excludes_four_fifths (floor : ratio_floor) :
    excludes_four_fifths := by
  intro F G hF hG hcont hfourier hden
  have h := floor F G hF hG hcont hfourier hden
  norm_num at h ⊢
  linarith

end CMSFunctionalObstruction.v1

#print axioms CMSDualCertificate.v1.challenge_integral_witness
#print axioms CMSFunctionalObstruction.v1.challenge_ratio_floor
#print axioms CMSFunctionalObstruction.v1.challenge_excludes_four_fifths
