/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BRSourceInterfaces
import ExplicitPopulationSourceWitness
import ExplicitFlatPopulationSourceWitness

set_option autoImplicit false
noncomputable section
namespace RH080Next.PopulationCanonical

/-- The canonical fingerprinted input table is exactly the actual C program's
model input, not a numerically nearby re-optimization or normalization. -/
theorem sparse_nodes_exact :
    AffineFourierPrograms.v1.sparseNodes = PopulationPV.nodes := rfl

theorem flat_nodes_exact :
    AffineFourierPrograms.v1.flatNodes = FlatPopulationPV.nodes := rfl

end RH080Next.PopulationCanonical
namespace AffineFourierPrograms.v1

/-- Complete source-first numerical provider, combined with the actual Fourier,
leakage, maximum and normalization proofs. The literature norm identity is an
explicit network input. Compilation/runtime/hardware remain the declared trust
boundary, not extra mathematical premises or unverified answer literals. -/
theorem challenge_sparse_witness (hNorm : BRFourierInput.v1.norm_identity) :
    sparse_witness := by
  change IEANTN.CMSFunctional.Eligible RH080Next.PopulationWitness.amplitude
    RH080Next.PopulationWitness.window ∧ _
  exact ⟨RH080Next.PopulationWitness.actual_eligible,
    RH080Next.PopulationWitness.source_first_amplitude_norm_le hNorm,
    RH080Next.PopulationWitness.actual_positive_leakage,
    RH080Next.PopulationWitness.amplitude_zero,
    RH080Next.PopulationWitness.window_abs_le,
    RH080Next.PopulationWitness.window_peak_attained⟩

theorem challenge_flat_witness (hNorm : BRFourierInput.v1.norm_identity) :
    flat_witness := by
  change IEANTN.CMSFunctional.Eligible RH080Next.FlatPopulationWitness.amplitude
    RH080Next.FlatPopulationWitness.window ∧ _
  exact ⟨RH080Next.FlatPopulationWitness.actual_eligible,
    RH080Next.FlatPopulationWitness.actual_amplitude_norm_le hNorm
      RH080Next.FlatPopulationPV.source_first_periodic_norm,
    RH080Next.FlatPopulationWitness.actual_positive_leakage,
    RH080Next.FlatPopulationWitness.amplitude_zero,
    RH080Next.FlatPopulationWitness.window_abs_le,
    RH080Next.FlatPopulationWitness.window_peak_attained⟩

#print axioms challenge_sparse_witness
#print axioms challenge_flat_witness
end AffineFourierPrograms.v1
