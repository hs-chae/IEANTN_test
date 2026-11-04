/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.FKS2.v2.Conclusions
import IEANTN.Nodes.BKLNW.v1.Conclusions

/-! Conservative extension of the original FKS2 correction, with coefficient anchor30 fixed.
The application threshold L is independent of that coefficient anchor. -/
namespace FKS2Numerics.v3
open IEANTN Real

noncomputable def nuStar (A L : ℝ) : ℝ :=
  FKS2.v2.nuAsymp A (3 / 2) 2 5.5666305 (1 + 1.93378e-8) (BKLNW.v1.a₂ 30) (exp L)

/-- Preserved historical mathematical instance; the original raw constant is unchanged.

Spelled out: `ν*(A, L)` is FKS2's multiplier `ν_asymp` (FKS2.v2). It is how much an admissible
bound `A (log x/R)^{3/2} e^{−2√(log x/R)}` for `Eψ` must be inflated, as `A(1 + ν)`, to bound `Eθ`
for `x ≥ e^L`, with `R = 5.5666305`. This conclusion is the corrected Corollary 14 value
`ν*(121.096, 30) ≤ 6.339·10⁻⁷`. The printed `6.3376·10⁻⁷` is refuted
(`FKS2Scalar.original_threshold_discrepancy`).

Its designated proof uses the modelled summation and its error theorem, but no C source text
(evidence method `not-program-verified`). See `docs/program-verification/PV_HUMAN_READABLE_GUIDE.md`
and the local attestation in `pv-evidence/`. -/
def calibration_bound : Prop := nuStar 121.096 30 ≤ 6.339e-7

/-- Baseline numerical obligation on the common exp300tail, before any QRH update.

Spelled out: `ν*(121.096, 300) ≤ 1.1·10⁻⁶¹`, the ψ-to-θ multiplier on the tail `x ≥ e^300` for
FKS's classical ψ constant `121.096`. `FKS2.v4` consumes it to get a θ bound and prime intervals
`(x, x + x/16]` for `x ≥ e^300`. Checked by executing `Solutions/FKS2Numerics.v3/c/baseline.c` in
the RN64 model. The executed program equals the formal one only if their tokens match. A generic
summation error theorem carries the output to this inequality. The finite `native_decide` facts
are listed in the local attestation (`pv-evidence/`); there is no official Comparator receipt. -/
def baseline_bound : Prop := nuStar 121.096 300 ≤ (11 : ℝ) / 10 ^ 62

end FKS2Numerics.v3
