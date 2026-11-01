/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.ZeroFreeHalfPlane

/-! A sharper specialization of the proved paired QRH transfer above exp300.
The earlier whole-exp128 contract remains preserved in CH2.v8. -/
namespace CH2.v9

/-- Pair reflected zeros with multiplicities and apply the general CH2 formula. -/
def refined_transfer : Prop :=
  IEANTN.ZetaZeroFreeHalfPlane (7 / 8) → ∀ x : ℝ, Real.exp 300 ≤ x →
    IEANTN.Eψ x ≤ (1 / 566) * Real.log x ^ (2 : ℕ) * x ^ (-(1 : ℝ) / 8)

end CH2.v9
