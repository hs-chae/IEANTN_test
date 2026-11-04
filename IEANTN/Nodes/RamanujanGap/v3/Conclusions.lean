/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import IEANTN.Nodes.RamanujanGap.v1.Conclusions
import IEANTN.Nodes.RamanujanNumerics.v3.Conclusions
/-! The `RamanujanGap.v2` consequences on the range `x > exp 401` of `RamanujanNumerics.v3`. -/
namespace RamanujanGap.v3
open Real IEANTN RamanujanGap.v1 RamanujanNumerics.v3
/-- Certified normalized shortfall on the range of the QRH π input.

Spelled out: for every real `x > exp 401`, `loss x ≤ 9.988 / log x`, where
`gap x = (e·x/log x)·π(x/e) − π(x)²` and `loss x = max 0 (1 − (log x)⁶/x² · gap x)` are
`RamanujanGap.v1`'s definitions and `allowance = 9.988` is `RamanujanNumerics.v3`'s.
`RamanujanGap.v2` has `9.101` here but only for `x > exp 3915`. Premises: the QRH-derived π
expansion `DudekPlattNumerics.v5.pi_two_sided_qrh` (coefficients 119/131 above `exp 400`) and the
program-checked budget `RamanujanNumerics.v3.epsilon_budget`. -/
def loss_bound : Prop := ∀ x>exp 401,loss x≤allowance/log x
/-- Lower bound on the Ramanujan prime-counting expression on the same range.

Spelled out: for every real `x > exp 401`,
`(1 − 9.988/log x) · x²/(log x)⁶ < (e·x/log x)·π(x/e) − π(x)²`, on the same premises. The lower π
bound is applied at `x/e`, one unit lower in `log x`; it holds there because `x/e > exp 400`. -/
def gap_lower_bound : Prop := ∀ x>exp 401,
  (1-allowance/log x)*x^2/log x^6<gap x
/-- Ramanujan's inequality on the same range, under the same premises.

Spelled out: for every real `x > exp 401`, `π(x)² < (e·x/log x)·π(x/e)`. It follows from
`gap_lower_bound`, because `9.988/log x < 1` there. `RamanujanGap.v1.ramanujan` states it for
`x > exp 3915` under older premises. Conditional on the QRH-derived input; not a claim about the
literature's best range. -/
def ramanujan : Prop := ∀ x>exp 401,primeCounting x^2<exp 1*x/log x*primeCounting (x/exp 1)
end RamanujanGap.v3
