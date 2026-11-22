/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# A fixed zero-free half-plane

The boundary is open. The meromorphic pole at `1` is excluded explicitly, independently of the
value assigned there by a totalized zeta function. This does not assert RH at any finite height.
-/

namespace IEANTN

/-- The meromorphic zeta function is nonzero in `Re s > β`, apart from its pole. -/
def ZetaZeroFreeHalfPlane (β : ℝ) : Prop :=
  ∀ s : ℂ, β < s.re → s ≠ 1 → riemannZeta s ≠ 0

end IEANTN
