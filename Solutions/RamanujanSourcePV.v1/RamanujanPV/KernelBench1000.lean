/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.CheckerExecution
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RamanujanPV.KernelBench1000
/-- Ordinary kernel arithmetic; no native execution axiom. -/
theorem count : Nat.primeCounting 1000=168 := by decide +kernel
/-- Actual source-bound body execution returns the same independently
kernel-proved exact prime count. Physical C run association is recorded by
source and executable/output hashes, not asserted as a Lean platform axiom. -/
theorem source_run (heap : AST.C.Heap) :
    ∃t, AST.C.Run AST.C.service (AST.C.stmt Source.countFunction.body)
      (AST.C.countInput 1000 heap) (.returned t 168) ∧t.heap=heap := by
  have run := (AST.C.source_count_is_primeCounting 1000 (by decide) heap).2.1
  simpa only [count] using run
#print axioms count
#print axioms source_run
end RamanujanPV.KernelBench1000
