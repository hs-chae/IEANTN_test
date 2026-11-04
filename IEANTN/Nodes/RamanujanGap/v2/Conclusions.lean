/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RamanujanGap.v1.Conclusions
import IEANTN.Nodes.RamanujanNumerics.v2.Conclusions
/-! Matched-domain quantitative update, using exactly the old normalized gap/loss definitions. -/
namespace RamanujanGap.v2
open Real IEANTN RamanujanGap.v1 RamanujanNumerics.v2
/-- Smaller certified normalized shortfall, on the identical strict whole ray.

Spelled out: for every real `x > exp 3915`, `loss x ≤ 9.101 / log x`, where
`gap x = (e·x/log x)·π(x/e) − π(x)²` and `loss x = max 0 (1 − (log x)⁶/x² · gap x)` are
`RamanujanGap.v1`'s definitions and `allowance = 9.101` is `RamanujanNumerics.v2`'s. The old version
has `3914.7` in place of `9.101`. Premises: the QRH-derived π expansion
`DudekPlattNumerics.v5.pi_two_sided_qrh` (coefficients 119/131 above `exp 400`) and the
program-checked budget `RamanujanNumerics.v2.epsilon_budget`. Walkthrough:
`docs/qrh/RAMANUJAN_WALKTHROUGH.md`. -/
def loss_bound : Prop := ∀ x>exp 3915,loss x≤allowance/log x
/-- Stronger lower bound on the actual Ramanujan prime-counting expression.

Spelled out: for every real `x > exp 3915`,
`(1 − 9.101/log x) · x²/(log x)⁶ < (e·x/log x)·π(x/e) − π(x)²`, on the same premises as
`loss_bound`. The lower π bound is applied at `x/e`, one unit lower in `log x`. The v5 input
covers that point, because it holds from `exp 400`. -/
def gap_lower_bound : Prop := ∀ x>exp 3915,
  (1-allowance/log x)*x^2/log x^6<gap x
/-- Both source-derived claims under a common stronger analytic premise. -/
def paired : Prop := RamanujanGap.v1.loss_bound ∧ RamanujanGap.v1.gap_lower_bound ∧
  loss_bound ∧ gap_lower_bound
/-- A comparison of certified allowances, not a ratio of actual errors. -/
def strict_allowance_improvement : Prop := ∀ x>exp 3915,allowance/log x<3914.7/log x
end RamanujanGap.v2
