/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyAsymptoticPopulation
import AnalyticFlatFamilyPopulation
import AnalyticFlat64Population
import BRSourceInterfaces
import IEANTN.Nodes.RHAnalyticFlatPopulation.v1.Conclusions
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real IEANTN.CMSFunctional Filter
open scoped Topology
namespace RHAnalyticFlatPopulation.v1

/-- Pure analytic kernel route, not source-first program verification. -/
theorem challenge_family_curve
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) : family_curve := by
  intro m hm α hα ε hε
  simpa only [familyWidth,RH080Next.AnalyticFlatFamily.width,RH080Next.AnalyticFlatFamily.order] using
    RH080Next.AnalyticFlatFamily.actual_population_curve hNorm hUniform hRH m hm α ε hα hε

theorem challenge_family_infimum (hFamily : family_curve) : family_infimum := by
  intro m hm α hα
  have hne : (goodCoefficients α).Nonempty :=
    ⟨familyWidth m α+1,hFamily m hm α hα 1 (by norm_num)⟩
  refine ⟨hne,?_⟩
  have hb : BddBelow (goodCoefficients α) := ⟨0,fun _ hc=>hc.1.le⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  exact csInf_le hb (hFamily m hm α hα ε hε)

theorem challenge_flat64_curve
    (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) : flat64_curve := by
  intro α hα
  exact RH080Next.AnalyticFlat64.actual_population_curve hNorm hUniform hRH α hα

theorem challenge_forty_population (hFlat : flat64_curve) : forty_population := by
  have h:=hFlat 40 (by norm_num)
  norm_num [flat64Width] at h
  exact h

#print axioms challenge_family_curve
#print axioms challenge_family_infimum
#print axioms challenge_flat64_curve
#print axioms challenge_forty_population

theorem challenge_adaptive_limit : adaptive_limit := by
  exact RH080Next.AnalyticFlatFamilyAsymptotic.width_offset_tendsto

/-- Canonical graph propagation uses the actual family and limit statements
as proof arguments, rather than assuming an asymptotic population conclusion. -/
theorem challenge_adaptive_population (hFamily : family_curve)
    (hLimit : adaptive_limit) : adaptive_population := by
  intro η hη
  have hsmall : ∀ᶠα:ℝ in atTop,
      familyWidth (adaptiveMesh α) α-α-log α/Real.pi<asymptoticConstant+η :=
    (tendsto_order.1 hLimit).2 _ (by linarith)
  filter_upwards [hsmall,eventually_gt_atTop (0:ℝ)] with α hw hα
  have hε : 0<(α+log α/Real.pi+asymptoticConstant+η)-familyWidth (adaptiveMesh α) α := by linarith
  have h:=hFamily (adaptiveMesh α) (by unfold adaptiveMesh;omega) α hα.le
    ((α+log α/Real.pi+asymptoticConstant+η)-familyWidth (adaptiveMesh α) α) hε
  rw [show familyWidth (adaptiveMesh α) α+
    ((α+log α/Real.pi+asymptoticConstant+η)-familyWidth (adaptiveMesh α) α)=
    α+log α/Real.pi+asymptoticConstant+η by ring] at h
  exact h

#print axioms challenge_adaptive_limit
#print axioms challenge_adaptive_population

end RHAnalyticFlatPopulation.v1
