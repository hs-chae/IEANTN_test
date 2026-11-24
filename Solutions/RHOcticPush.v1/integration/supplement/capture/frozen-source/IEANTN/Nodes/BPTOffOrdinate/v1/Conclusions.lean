/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ZeroCount.v1.Conclusions
namespace BPTOffOrdinate.v1
/-- Common off-ordinate part of Brent--Platt--Trudgian Corollary1:
for T>2π not a positive zero ordinate, |N(T)-main(T)|≤0.28logT.
No choice of convention at a zero height is assumed; a separate proved right
limit transfers this to the closed count without a new allowance. -/
def bound : Prop := ∀ T : ℝ, 2 * Real.pi < T →
  (∀ z : ℂ, riemannZeta z = 0 → 0 < z.im → z.im ≠ T) →
    |ZeroCount.v1.zetaNClosed T - ZeroCount.v1.rvmMain T| ≤ (7 / 25) * Real.log T
end BPTOffOrdinate.v1
