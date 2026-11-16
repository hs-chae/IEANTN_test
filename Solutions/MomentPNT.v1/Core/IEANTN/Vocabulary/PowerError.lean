/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms

/-! One power/logarithm bound shape shared by psi, theta, pi and prime-gap consumers. -/
namespace IEANTN

/-- A uniform bound A*(log x)^k*x^(beta-1) above a supplied threshold.
The natural logarithm power is a natural number. Decay needs beta<1 and x>1;
those are explicit hypotheses of the conversion theorems, not implicit conventions. -/
def HasPowerLogBound (E : ℝ → ℝ) (A : ℝ) (k : ℕ) (β x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, E x ≤ A * Real.log x ^ k * x ^ (β - 1)

end IEANTN
