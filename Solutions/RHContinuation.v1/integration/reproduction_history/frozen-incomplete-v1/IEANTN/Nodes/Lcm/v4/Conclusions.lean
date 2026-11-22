/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.RHSmoothing
namespace Lcm.v4
open Real IEANTN.RHSmoothing
/-- Actual lcm logarithmic growth, preserving the complete new PNT envelope. -/
def box_growth : Prop := ∀ n : ℕ, exp 35 ≤ (n : ℝ) →
  |log (Nat.lcmUpto n : ℝ) - n| ≤ sqrt n * fastBound (log n)
/-- Independent, more fully kernel-closed CH-route envelope with an earlier onset. -/
def recovered_growth : Prop := ∀ n : ℕ, exp 34 ≤ (n : ℝ) →
  |log (Nat.lcmUpto n : ℝ) - n| ≤ chBound (log n) * sqrt n
end Lcm.v4
