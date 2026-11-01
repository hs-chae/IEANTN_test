/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.ZetaHadamard.v1.Conclusions

/-! The existing weighted identity on a domain where QRH supplies nonvanishing.
The algebraic identity and source formula are unchanged; this is a derived interface. -/
namespace ZetaHadamard.v2
open IEANTN

/-- QRH discharges the old pointwise nonzero guards on its open half-plane. -/
noncomputable def halfplane_partial_fractions : Prop :=
  ∀ s w : ℂ, (7 / 8 : ℝ) < s.re → (7 / 8 : ℝ) < w.re → s ≠ 1 → w ≠ 1 →
    HasSum (fun ρ : zetaZeroesIn (Set.Ioo (0:ℝ) 1) Set.univ ↦
        (1 / (s - (ρ : ℂ)) - 1 / (w - (ρ : ℂ))) * (zetaOrder (ρ : ℂ) : ℂ))
      (deriv riemannZeta s / riemannZeta s - deriv riemannZeta w / riemannZeta w
        + (Complex.digamma (s / 2 + 1) - Complex.digamma (w / 2 + 1)) / 2
        + 1 / (s - 1) - 1 / (w - 1))

end ZetaHadamard.v2
