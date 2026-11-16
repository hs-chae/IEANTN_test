/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.ZeroFreeHalfPlane
import IEANTN.Nodes.FKS.v3.Conclusions
import IEANTN.Nodes.CH2.v6.Tables

/-! Optimized CH2 transfers. `Derivation.html` explains the estimates. Complete named-input
Lean proofs are in `Solutions/CH2.v6/PairedSolution.lean` and `DensitySolution.lean`.
Official Comparator receipts are still pending. -/
namespace CH2.v6

/-- Same-input refinement: retain the zero-count polynomial, pair reflected zeros, and sharpen
the pole correction. The analytic argument, numerical endpoint arithmetic and full-range
continuation are proved together by the named-input Lean solution. -/
def paired_transfer : Prop :=
  IEANTN.ZetaZeroFreeHalfPlane (7 / 8) → ∀ x : ℝ, Real.exp 128 ≤ x →
    IEANTN.Eψ x ≤ (1 / 384) * Real.log x ^ (2 : ℕ) * x ^ (-(1 : ℝ) / 8)

/-- Add corrected explicit density and finite-height RH, split zeros at real part `3/4`,
and integrate the right-side density. Each table row controls every x above its threshold.
The coefficient has no growing logarithmic factor. Domain and constants are derived here,
not attributed as a verbatim theorem of CH2, FKS or OpenAI. -/
def density_transfer : Prop :=
  FKS.v3.density_0618 → IEANTN.RiemannHypothesisUpTo (3 * (10 : ℝ) ^ (12 : ℕ)) →
    IEANTN.ZetaZeroFreeHalfPlane (7 / 8) →
      ∀ L C : ℝ, (L, C) ∈ densityFrontier → ∀ x : ℝ, Real.exp L ≤ x →
        IEANTN.Eψ x ≤ C * x ^ (-(1 : ℝ) / 8)

end CH2.v6
