/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHOcticEvolution

namespace RHSmoothing.v2
open Real IEANTN.RHOcticEvolution
/-- Whole-real-ray actual psi envelope. The exact analytic inputs are separate graph edges. -/
def box_psi : Prop := ∀ x : ℝ, exp 35 ≤ x →
  |Chebyshev.psi x - x| ≤ sqrt x * boxBound (log x)
/-- Exact difference between complete old and new box functions, not actual errors. -/
def box_gain : Prop := ∀ L : ℝ,
  IEANTN.RHSmoothing.fastBound L - boxBound L = (1 / 25000) / Real.pi
end RHSmoothing.v2
