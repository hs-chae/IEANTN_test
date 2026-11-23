/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RH.v1.Conclusions

/-! # Logical consequences of the explicit RH input

Only hypothesis plumbing is recorded. No analytic bounds or numerical zero data are supplied.
-/
namespace RHAdapters.v1

/-- RH implies every existing open half-plane with boundary at least 1/2.
The boundary is not excluded; the pole at 1 is explicitly allowed. -/
def half_planes : Prop :=
  ∀ β : ℝ, (1 / 2 : ℝ) ≤ β → IEANTN.ZetaZeroFreeHalfPlane β

/-- RH implies every existing finite-height empty rectangle, without an infinite height. -/
def finite_heights : Prop := ∀ T : ℝ, IEANTN.RiemannHypothesisUpTo T

end RHAdapters.v1
