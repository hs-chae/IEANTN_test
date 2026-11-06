/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.RayProgram
namespace PVEvolutionA.Recovery.Ray
set_option maxHeartbeats 0
set_option maxRecDepth 200000

/-- A concrete fresh run, not an imported Arb assertion. Every term's interval
domain flag and both row upper bounds must be checked by the actual evaluator. -/
theorem checked : WinnerProgramA.acceptUpper output bounds=true := by native_decide

#print axioms checked
end PVEvolutionA.Recovery.Ray
