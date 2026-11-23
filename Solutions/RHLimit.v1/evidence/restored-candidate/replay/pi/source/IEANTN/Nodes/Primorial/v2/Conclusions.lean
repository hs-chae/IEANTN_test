/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
namespace Primorial.v2
open Real IEANTN.RHSmoothing
/-- Actual primorial growth, after accounting for prime powers by the existing theta relay. -/
def box_growth : Prop := ∀ n : ℕ, exp 35 ≤ (n : ℝ) →
  |log (primorial n : ℝ) - n| ≤ (fastBound (log n) + 101 / 100) * sqrt n
end Primorial.v2
