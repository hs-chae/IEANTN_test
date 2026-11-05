/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Configuration
import PVEvolutionA.Evaluator
namespace PVEvolutionA.SlopedRay300
open WinnerProgramA
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def program := Configuration.program 0
def bounds := Configuration.bounds 0
/-- A genuine fresh run. Domain flags and both row enclosures must pass. -/
theorem checked : acceptUpper (Evaluator.run program) bounds=true := by native_decide
theorem coefficient : Separated.coefficient 65536 300 100 ≤ (9468285637/1000000000000:ℝ) := by
  have hh:=Evaluator.source_linked_upper program bounds checked
  rw [show program=Separated.program 300 100 65536 from rfl,
    Separated.program_semantics _ _ (by decide : 0<(65536:ℕ)) (by norm_num)] at hh
  norm_num [bounds,Configuration.bounds] at hh ⊢
  exact hh
#print axioms coefficient
end PVEvolutionA.SlopedRay300
