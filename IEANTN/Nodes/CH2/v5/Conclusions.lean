/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.ErrorTerms
import IEANTN.Vocabulary.ZeroFreeHalfPlane

/-!
# Node `CH2.v5`: a fixed-strip consequence of the CH2 formula

A reusable pipeline derived from Chirre--Helfgott, arXiv:2512.15709v1, Theorem 1.1 (1.2),
with Lemma C.1, Proposition 8.8 and the elementary zero estimates in Appendix B.

The coefficient and threshold are derived here; they are NOT a transcription of Corollary 1.2,
whose hypothesis is RH up to `T`. `Derivation.html` gives the written derivation, including the
choice of a height away from zero ordinates. The complete named-input Lean proof is in
`Solutions/CH2.v5/GeneralStripSolution.lean`; its official Comparator receipt is still pending.

Keeping `β` free permits later fixed-half-plane improvements to be substituted without repeating
these estimates. The result is deliberately conservative. No novelty or optimality is claimed.
-/

namespace CH2.v5

/-- **Derived fixed-strip estimate.** If `1/2 ≤ β < 1` and `ζ` is zero-free in `Re s > β`, then
`Eψ x ≤ 2 (1-β)^2 (log x)^2 x^(β-1)` for `x ≥ exp(16/(1-β))`.

Use the finite spectral formula at a height in `[x^(1-β), x^(1-β)+1]`.
Zeros on `Re s = β` are permitted. -/
def psi_bound_of_fixed_strip : Prop :=
  ∀ β : ℝ, (1 / 2 : ℝ) ≤ β → β < 1 → IEANTN.ZetaZeroFreeHalfPlane β →
    ∀ x : ℝ, Real.exp (16 / (1 - β)) ≤ x →
      IEANTN.Eψ x ≤ 2 * (1 - β) ^ (2 : ℕ) * Real.log x ^ (2 : ℕ) * x ^ (β - 1)

end CH2.v5
