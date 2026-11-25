/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Primal56NumericalWitness
import Primal56Objective
import Primal56CanonicalConsumers

noncomputable section
set_option autoImplicit false
open Real Filter IEANTN.CMSFunctional
namespace RH080.Primal56Gap

/-- Closed numerical objective: the real Fourier and whole-line integral
proofs are consumed rather than supplied as mathematical assumptions. -/
theorem actual_objective_witness : GaussianFourierWitness.v3.objective_witness :=
  GaussianFourierWitness.v3.challenge_objective_witness
    GaussianFourierWitness.v3.challenge_integral_fourier_witness

/-- Source-enriched ordinary-RH asymptotic result at the exact certified
fraction. Only the unchanged general CMS source reduction and RH remain. -/
theorem actual_normalized_gap (hCMS : CMSFunctionalInput.v1.gap_reduction)
    (rh : RH.v1.hypothesis) : RHAsymptoticGaussian.v3.normalized_gap :=
  RHAsymptoticGaussian.v3.challenge_normalized_gap hCMS rh actual_objective_witness

theorem actual_gap_below_readable (hCMS : CMSFunctionalInput.v1.gap_reduction)
    (rh : RH.v1.hypothesis) : RHAsymptoticGaussian.v3.gap_below_readable :=
  RHAsymptoticGaussian.v3.challenge_gap_below_readable (actual_normalized_gap hCMS rh)

theorem actual_gap_below_v2 (hCMS : CMSFunctionalInput.v1.gap_reduction)
    (rh : RH.v1.hypothesis) : RHAsymptoticGaussian.v3.gap_below_v2 :=
  RHAsymptoticGaussian.v3.challenge_gap_below_v2 (actual_normalized_gap hCMS rh)

theorem actual_gap_below_v1 (hCMS : CMSFunctionalInput.v1.gap_reduction)
    (rh : RH.v1.hypothesis) : RHAsymptoticGaussian.v3.gap_below_v1 :=
  RHAsymptoticGaussian.v3.challenge_gap_below_v1 (actual_normalized_gap hCMS rh)

theorem actual_gap_below_printed_2026 (hCMS : CMSFunctionalInput.v1.gap_reduction)
    (rh : RH.v1.hypothesis) : RHAsymptoticGaussian.v3.gap_below_printed_2026 :=
  RHAsymptoticGaussian.v3.challenge_gap_below_printed_2026 (actual_normalized_gap hCMS rh)

theorem actual_population_curve (hCMS : CMSFunctionalInput.v1.population_reduction)
    (rh : RH.v1.hypothesis) : RHAsymptoticGaussian.v3.population_curve :=
  RHAsymptoticGaussian.v3.challenge_population_curve hCMS rh actual_objective_witness

theorem actual_population_count (hCMS : CMSFunctionalInput.v1.population_reduction)
    (rh : RH.v1.hypothesis) : RHAsymptoticGaussian.v3.population_count :=
  RHAsymptoticGaussian.v3.challenge_population_count (actual_population_curve hCMS rh)

#print axioms actual_objective_witness
#print axioms actual_normalized_gap
#print axioms actual_population_curve
#print axioms actual_population_count
end RH080.Primal56Gap
