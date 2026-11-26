/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PopulationExecution
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.PopulationPV.Execution
/-- Execution of the actual fixed-input C numerical algorithm through its
source-derived AST. The enclosure's mathematical meaning is proved separately. -/
theorem actual_norm_program :
    call 10000 "population_norm_upper" [] = some 887721072633027910 := by
  decide +kernel
#print axioms actual_norm_program
end RH080Next.PopulationPV.Execution
