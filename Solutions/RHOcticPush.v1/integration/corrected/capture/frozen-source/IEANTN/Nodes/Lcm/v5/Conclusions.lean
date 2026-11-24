/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHOcticEvolution
namespace Lcm.v5
open Real IEANTN.RHOcticEvolution
/-- Actual lcm logarithmic growth with the entire improved box function. -/
def box_growth : Prop := ∀ n : ℕ, exp 35 ≤ (n : ℝ) →
  |log (Nat.lcmUpto n : ℝ) - n| ≤ sqrt n * boxBound (log n)
/-- The independent existing CH profile is preserved with its own earlier onset. -/
def recovered_growth : Prop := ∀ n : ℕ, exp 34 ≤ (n : ℝ) →
  |log (Nat.lcmUpto n : ℝ) - n| ≤ IEANTN.RHSmoothing.chBound (log n) * sqrt n
end Lcm.v5
