/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHOcticEvolution
namespace Primorial.v3
open Real IEANTN
/-- Actual primorial growth with the tighter same-source box coefficient. -/
def box_growth : Prop := ∀ n : ℕ, exp 35 ≤ (n : ℝ) →
  |log (primorial n : ℝ) - n| ≤
    (RHOcticEvolution.boxBound (log n) + 101 / 100) * sqrt n
end Primorial.v3
