/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FlatPopulationNorm
namespace RH080Next.FlatPopulationPV
open MeasureTheory
/-- Matched kernel-only mathematical control. Same input, grid, arithmetic,
allowances and final bound; no C source or source-execution theorem imported. -/
theorem kernel_only_periodic_norm :
    (∫ y in (0 : ℝ)..1, |Model.trigPolynomial y|) ≤
      (1120475208606944546 : ℝ)/1000000000000000000 := by
  simpa only [Model.normUpper_exact, Nat.cast_ofNat] using Model.periodic_norm_upper
#print axioms kernel_only_periodic_norm
end RH080Next.FlatPopulationPV
