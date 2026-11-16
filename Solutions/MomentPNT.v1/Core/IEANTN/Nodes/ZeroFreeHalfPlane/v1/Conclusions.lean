/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ZeroFreeHalfPlane
import IEANTN.Vocabulary.Zeta
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! General interfaces; none of the quantified beta values is asserted to be known. -/
namespace ZeroFreeHalfPlane.v1
open Real IEANTN

/-- The right-hand strict zero count vanishes at or to the right of a zero-free boundary. -/
def density_vanishes : Prop :=
  ∀ β σ T : ℝ, ZetaZeroFreeHalfPlane β → β ≤ σ → zetaN' σ T = 0

/-- An open half-plane implies a closed classical region strictly inside it. -/
def classical_region : Prop :=
  ∀ β R t₀ : ℝ, β < 1 → 0 < R → 1 < t₀ →
    1 / (R * (1 - β)) < log t₀ → ZetaZeroFreeHalfPlane β → ClassicalZeroFreeRegion R t₀

/-- Reciprocal zeta is holomorphic away from its pole on the supplied half-plane. -/
def reciprocal_differentiable : Prop :=
  ∀ β : ℝ, ZetaZeroFreeHalfPlane β →
    DifferentiableOn ℂ (fun s : ℂ ↦ (riemannZeta s)⁻¹) {s | β < s.re ∧ s ≠ 1}

end ZeroFreeHalfPlane.v1
