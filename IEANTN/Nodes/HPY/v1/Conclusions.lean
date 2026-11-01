/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta

/-! Hiary, Patel and Yang, arXiv:2207.02366v1, Theorem 1.1. Source statement only. -/
namespace HPY.v1

/-- Theorem 1.1: the corrected and improved subconvexity constant `0.618`, for every `t ≥ 3`.
This is a cited source claim, not a locally replayed formal proof. -/
def subconvexity_bound : Prop :=
  ∀ t : ℝ, 3 ≤ t →
    ‖riemannZeta (1 / 2 + t * Complex.I)‖ ≤ 0.618 * t ^ ((1 : ℝ) / 6) * Real.log t

end HPY.v1
