/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlatFamilyAsymptoticLimits

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real Filter RH080Next.Explicit
open scoped Topology
namespace RH080Next.AnalyticFlatFamilyAsymptotic
open RH080Next.AnalyticFlatFamily

/-- Positive additive allowances in the density coefficient absorb the proved
 vanishing analytic remainder; this is a full real-density eventual statement. -/
theorem width_eventually_lt (η : ℝ) (hη : 0<η) :
    ∀ᶠ α : ℝ in atTop,
      width (mesh α) α<α+Real.log α/Real.pi+constant+η := by
  have h := (tendsto_order.1 width_offset_tendsto).2 (constant+η) (by linarith)
  filter_upwards [h] with α hα
  linarith

/-- For every fixed positive coefficient allowance, all sufficiently large
 real densities have an actual strict eventual prime-population margin.
 The eventual prime-variable onset may depend on density and allowance.
 This is kernel-only analytic mathematics, not source-first PV. -/
theorem actual_population_curve (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ α : ℝ in atTop,
      IEANTN.CMSFunctional.GoodCoefficient α
        (α+Real.log α/Real.pi+constant+η) := by
  filter_upwards [width_eventually_lt η hη,eventually_gt_atTop (0:ℝ)] with α hw hα
  have he : 0<(α+Real.log α/Real.pi+constant+η)-width (mesh α) α := by linarith
  have h := RH080Next.AnalyticFlatFamily.actual_population_curve hNorm hUniform hRH
    (mesh α) (mesh_positive α) α
    ((α+Real.log α/Real.pi+constant+η)-width (mesh α) α) hα.le he
  rw [show width (mesh α) α+((α+Real.log α/Real.pi+constant+η)-width (mesh α) α)=
    α+Real.log α/Real.pi+constant+η by ring] at h
  exact h

/-- The same concrete rounded-mesh witnesses prove nonemptiness as well as
 the population infimum bound, so the empty-set infimum convention is unused.
 No zero-allowance endpoint or optimality is asserted. -/
theorem actual_population_infimum (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ α : ℝ in atTop,
      (IEANTN.CMSFunctional.goodCoefficients α).Nonempty ∧
        sInf (IEANTN.CMSFunctional.goodCoefficients α)≤
          α+Real.log α/Real.pi+constant+η := by
  filter_upwards [width_eventually_lt η hη,eventually_gt_atTop (0:ℝ)] with α hw hα
  obtain ⟨hne,hi⟩ := RH080Next.AnalyticFlatFamily.actual_population_infimum
    hNorm hUniform hRH (mesh α) (mesh_positive α) α hα.le
  exact ⟨hne,hi.trans hw.le⟩

/-- Unnormalized actual half-open count, retaining a positive population margin.
 The order of eventual quantifiers is density first, then the prime variable. -/
theorem actual_population_eventual (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (η : ℝ) (hη : 0<η) :
    ∀ᶠ α : ℝ in atTop, ∃δ : ℝ,0<δ ∧ ∀ᶠ x : ℝ in atTop,
      (α+δ)*sqrt x≤
        (IEANTN.CMSFunctional.halfOpenCount
          (α+Real.log α/Real.pi+constant+η) x:ℝ) := by
  filter_upwards [actual_population_curve hNorm hUniform hRH η hη] with α hα
  obtain ⟨δ,hδ,hcount⟩ := hα.2
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hcount,eventually_gt_atTop (0:ℝ)] with x hx hx0
  unfold IEANTN.CMSFunctional.normalizedPopulation at hx
  exact (le_div_iff₀ (sqrt_pos.2 hx0)).mp hx

#print axioms actual_population_curve
#print axioms actual_population_infimum
#print axioms actual_population_eventual
end RH080Next.AnalyticFlatFamilyAsymptotic
