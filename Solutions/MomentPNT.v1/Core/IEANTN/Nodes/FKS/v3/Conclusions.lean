/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.Zeta

/-! FKS, arXiv:2204.02588v3, Corollary 2.9 and Table 8, lower `a₁ = 0.618` panel.
The constants below round UP the largest source entries on `[3/4, 7/8]`.
They are not obtained by substituting 0.618 in the invalid old KLN tables. -/
namespace FKS.v3

/-- Uniform consequence of the source's Table 8: `c₁ ≤ 9.795`, `c₂ ≤ 4.465` on `[3/4, 7/8]`.
Height at least `3·10¹²`. Lean counts strict real and imaginary endpoints. The paper includes the real endpoint,
so its bound implies this weaker count; one-sided limits supply the closed height needed later.
The table is a cited numerical source input, not a recomputation or formal proof here. -/
def density_0618 : Prop :=
  ∀ σ T : ℝ, 3 / 4 ≤ σ → σ ≤ 7 / 8 → 3 * (10 : ℝ) ^ (12 : ℕ) ≤ T →
    IEANTN.zetaN' σ T ≤
      9.795 * T ^ (8 * (1 - σ) / 3) * (Real.log T) ^ (5 - 2 * σ)
        + 4.465 * Real.log T ^ (2 : ℕ)

end FKS.v3
