/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
/-! Preserved seven-term workload, instantiated only after the old baseline freeze. -/
namespace RamanujanNumerics.v2
open Real DudekPlatt.v3
/-- Deterministically rounded output-plus-error allowance; exact value from the new source certificate. -/
noncomputable def allowance : ℝ := (9101:ℝ)/1000
/-- Updated numerical majorant for the same repaired criterion and common full ray. -/
def epsilon_budget : Prop := ∀ x>exp 3915,
  εUpper 131 x-εLower 119 (exp 3914) x≤allowance
end RamanujanNumerics.v2
