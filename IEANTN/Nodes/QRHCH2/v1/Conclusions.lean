/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.OpenAIQRH.v1.Conclusions
import IEANTN.Nodes.CH2.v1.Conclusions
import IEANTN.Nodes.CH2.v5.Conclusions

/-!
# Node `QRHCH2.v1`

Specialize the fixed-strip pipeline to OpenAI's `7/8` half-plane, then intersect it with CH2's
existing Corollary 1.3. The upstream literature claim, named-input Lean transfer and short Lean
composition are separate pieces of evidence.

Here `Eψ x = |ψ(x)-x|/x`, so the first conclusion bounds the absolute PNT error by
`(1/32) x^(7/8) (log x)^2` for `x ≥ exp(128)`.
-/

namespace QRHCH2.v1

/-- The `7/8` specialization: `Eψ x ≤ (log x)^2 / (32 x^(1/8))` above `exp(128)`. -/
def psi_power_bound : Prop :=
  ∀ x : ℝ, Real.exp 128 ≤ x →
    IEANTN.Eψ x ≤ (1 / 32 : ℝ) * Real.log x ^ (2 : ℕ) * x ^ (-(1 / 8 : ℝ))

/-- Keep the better of CH2's existing finite-height bound and the new power-saving bound. -/
def psi_hybrid_bound : Prop :=
  ∀ x : ℝ, Real.exp 128 ≤ x →
    IEANTN.Eψ x ≤ min
      (Real.pi / (3 * (10 : ℝ) ^ (12 : ℕ)) + 113.67 / Real.sqrt x)
      ((1 / 32 : ℝ) * Real.log x ^ (2 : ℕ) * x ^ (-(1 / 8 : ℝ)))

end QRHCH2.v1
