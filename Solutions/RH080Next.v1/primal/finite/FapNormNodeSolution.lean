/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapSourceInterfaces
import IEANTN.Nodes.FapFourierNorm.v1.Conclusions
import FapFFTNorm

namespace RH080Next.Primal.FiniteCanonical

/-- Original fixed Fap nodes and the actual full-transform kernel certificate.
The literal BR norm identity remains the explicit canonical input. -/
theorem solution_l1_bound (h : BRFourierInput.v1.norm_identity) :
    FapFourierNorm.v1.l1_bound := by
  change (∫ u : ℝ, |RH080Next.Explicit.inverseCosine
    (RH080Next.Explicit.affineSpectrum FapFourierNorm.v1.Tables.affineNodes 80) u|) ≤ _
  rw [table_nodes_exact]
  exact RH080Next.Primal.FapFFTKernel.kernel_actual_norm h

end RH080Next.Primal.FiniteCanonical

namespace FapFourierNorm.v1

theorem challenge_l1_bound (h : BRFourierInput.v1.norm_identity) : l1_bound :=
  RH080Next.Primal.FiniteCanonical.solution_l1_bound h

end FapFourierNorm.v1
