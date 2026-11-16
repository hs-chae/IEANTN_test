/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! Actual seven-eighths consequences, with finite-height RH kept separate. -/
namespace QRHConsequences.v1
open Real IEANTN

/-- Zeros ON Re=7/8 are allowed; the strict count to its right is zero at every height. -/
def density_vanishes : Prop := ∀ σ T : ℝ, 7 / 8 ≤ σ → zetaN' σ T = 0

/-- A larger verified analytic domain for reciprocal zeta, without a pointwise nonzero input. -/
def reciprocal_differentiable : Prop :=
  DifferentiableOn ℂ (fun s : ℂ ↦ (riemannZeta s)⁻¹) {s | 7 / 8 < s.re ∧ s ≠ 1}

/-- R=1/3 above e^7, obtained by joining QRH above e^25 to existing finite-height RH.
This does not claim the same classical region at height 2. -/
def classical_region : Prop := ClassicalZeroFreeRegion (1 / 3) (exp 7)

/-- A closed classical region with R=3 at the original all-height threshold 2.
QRH provides the tail above e^3, and existing finite-height RH handles the rest. -/
def all_height_classical_region : Prop := ClassicalZeroFreeRegion 3 2

end QRHConsequences.v1
