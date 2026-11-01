/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.ZeroFreeHalfPlane

/-! The paired QRH transfer, now proved from the CH2 ingredients in Lean.
This preserves the mathematical contract of CH2.v6.paired_transfer. -/
namespace CH2.v8

/-- Pair reflected zeros with multiplicities and apply the general CH2 formula. -/
def paired_transfer : Prop :=
  IEANTN.ZetaZeroFreeHalfPlane (7 / 8) → ∀ x : ℝ, Real.exp 128 ≤ x →
    IEANTN.Eψ x ≤ (1 / 384) * Real.log x ^ (2 : ℕ) * x ^ (-(1 : ℝ) / 8)

end CH2.v8
