/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Graded
namespace PVEvolutionA.Ray300
open WinnerProgramA
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def program := gradedProgram 300 100 65536
def bounds : List ℚ := [3/1000000000000,9468680075/1000000000000]
/-- A genuine fresh run. Domain flags and both row enclosures must pass. -/
theorem checked : acceptUpper (run program) bounds=true := by native_decide
theorem coefficient : gradedCoefficient 65536 300 100 ≤ (9468680078/1000000000000:ℝ) := by
  have hh:=source_linked_upper program (run program) bounds rfl checked
  rw [show program=gradedProgram 300 100 65536 from rfl,
    graded_program_semantics _ _ (by decide : 0<(65536:ℕ)) (by norm_num)] at hh
  norm_num [bounds] at hh ⊢
  exact hh
#print axioms coefficient
end PVEvolutionA.Ray300
