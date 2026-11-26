/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WeightedPopulationSolution
import ExplicitPopulationControlWitness
import ExplicitFlatPopulationControlWitness
set_option autoImplicit false
noncomputable section
namespace RH080Next.PopulationCanonical

/-- Same exact input and numerical bound, with kernel-only numerical execution.
This is the matched mathematical control and is never described as source PV. -/
theorem kernel_only_sparse_witness (hNorm : BRFourierInput.v1.norm_identity) :
    AffineFourierPrograms.v1.sparse_witness := by
  change IEANTN.CMSFunctional.Eligible PopulationWitness.amplitude PopulationWitness.window ∧ _
  exact ⟨PopulationWitness.actual_eligible,
    PopulationWitness.kernel_only_amplitude_norm_le hNorm,
    PopulationWitness.actual_positive_leakage,PopulationWitness.amplitude_zero,
    PopulationWitness.window_abs_le,PopulationWitness.window_peak_attained⟩

theorem kernel_only_flat_witness (hNorm : BRFourierInput.v1.norm_identity) :
    AffineFourierPrograms.v1.flat_witness := by
  change IEANTN.CMSFunctional.Eligible FlatPopulationWitness.amplitude FlatPopulationWitness.window ∧ _
  exact ⟨FlatPopulationWitness.actual_eligible,
    FlatPopulationWitness.actual_amplitude_norm_le hNorm FlatPopulationPV.kernel_only_periodic_norm,
    FlatPopulationWitness.actual_positive_leakage,FlatPopulationWitness.amplitude_zero,
    FlatPopulationWitness.window_abs_le,FlatPopulationWitness.window_peak_attained⟩

/-- The exact same generic mathematical consumer closes both entire curves. -/
theorem kernel_only_frontier (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    RHWeightedPopulation.v1.frontier_curve :=
  RHWeightedPopulation.v1.challenge_frontier_curve
    (RHWeightedPopulation.v1.challenge_sparse_curve hUniform hRH
      (kernel_only_sparse_witness hNorm))
    (RHWeightedPopulation.v1.challenge_flat_curve hUniform hRH
      (kernel_only_flat_witness hNorm))

#print axioms kernel_only_sparse_witness
#print axioms kernel_only_flat_witness
#print axioms kernel_only_frontier
end RH080Next.PopulationCanonical
