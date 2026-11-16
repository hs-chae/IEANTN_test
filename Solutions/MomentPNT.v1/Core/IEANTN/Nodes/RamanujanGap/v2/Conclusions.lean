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
/-- Smaller certified normalized shortfall, on the identical strict whole ray. -/
def loss_bound : Prop := ∀ x>exp 3915,loss x≤allowance/log x
/-- Stronger lower bound on the actual Ramanujan prime-counting expression. -/
def gap_lower_bound : Prop := ∀ x>exp 3915,
  (1-allowance/log x)*x^2/log x^6<gap x
/-- Both source-derived claims under a common stronger analytic premise. -/
def paired : Prop := RamanujanGap.v1.loss_bound ∧ RamanujanGap.v1.gap_lower_bound ∧
  loss_bound ∧ gap_lower_bound
/-- A comparison of certified allowances, not a ratio of actual errors. -/
def strict_allowance_improvement : Prop := ∀ x>exp 3915,allowance/log x<3914.7/log x
end RamanujanGap.v2
