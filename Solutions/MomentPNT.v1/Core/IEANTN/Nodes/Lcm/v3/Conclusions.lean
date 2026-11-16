/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.Chebyshev

namespace Lcm.v3
open Real

/-- Derived Phase2 contract; exact named premises are recorded in metadata. -/
def log_growth : Prop :=
  ∀ n : ℕ, exp 192 ≤ (n : ℝ) →
    |log (Nat.lcmUpto n : ℝ) - n| ≤ 0.01713 * (n : ℝ) ^ (7 / 8 : ℝ)

end Lcm.v3
