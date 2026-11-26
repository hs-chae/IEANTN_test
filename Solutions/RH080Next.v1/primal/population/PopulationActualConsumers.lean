/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AffineProgramsSolution
import WeightedPopulationSolution

set_option autoImplicit false
noncomputable section
namespace RH080Next.PopulationCanonical
open IEANTN.CMSFunctional RHWeightedPopulation.v1

/-- Source-first executable outputs are consumed by both full numerical witness
packages, then by the ordinary-RH eventual actual-prime population theorem. -/
theorem source_first_sparse_curve (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    sparse_curve :=
  challenge_sparse_curve hUniform hRH
    (AffineFourierPrograms.v1.challenge_sparse_witness hNorm)

theorem source_first_flat_curve (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    flat_curve :=
  challenge_flat_curve hUniform hRH
    (AffineFourierPrograms.v1.challenge_flat_witness hNorm)

theorem source_first_frontier (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    frontier_curve :=
  challenge_frontier_curve (source_first_sparse_curve hNorm hUniform hRH)
    (source_first_flat_curve hNorm hUniform hRH)

theorem source_first_frontier_count (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    frontier_count :=
  challenge_frontier_count (source_first_frontier hNorm hUniform hRH)

theorem source_first_one_population (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    one_population :=
  challenge_one_population (source_first_sparse_curve hNorm hUniform hRH)

theorem source_first_ten_population (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    ten_population :=
  challenge_ten_population (source_first_flat_curve hNorm hUniform hRH)

#print axioms source_first_sparse_curve
#print axioms source_first_flat_curve
#print axioms source_first_frontier
#print axioms source_first_frontier_count
#print axioms source_first_one_population
#print axioms source_first_ten_population
end RH080Next.PopulationCanonical
