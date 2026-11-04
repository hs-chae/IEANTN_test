/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.DudekPlatt.v3.Conclusions
/-! Preregistered historical-input forward numerical experiment. -/
namespace RamanujanNumerics.v1
open Real DudekPlatt.v3
/-- Old selected numerical threshold majorant, reconstructed from the existing repaired criterion. -/
def epsilon_budget : Prop := ∀ x>exp 3915,
  εUpper 1426 x-εLower (-1194) (exp 3914) x≤3914.7
end RamanujanNumerics.v1
