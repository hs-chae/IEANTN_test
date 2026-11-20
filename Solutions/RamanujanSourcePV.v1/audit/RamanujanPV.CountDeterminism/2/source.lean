/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.CheckerExecution
import LCMSourcePV.ASTDeterminism
import RamanujanPV.Intervals

namespace RamanujanPV.AST.C
open LCMSourcePV.ASTLoops

theorem eval_deterministic (call : Service) : EvalDeterministic (Eval call) := by
  intro e s t value t' value' h h'
  have equal : (t,value)=(t',value') := Option.some.inj (h.symm.trans h')
  exact Prod.mk.inj equal

theorem declare_deterministic (call : Service) : DeclareDeterministic (Declare call) := by
  intro ds s t t' h h'
  exact Option.some.inj (h.symm.trans h')

theorem scope_deterministic : ScopeDeterministic Scope := by
  intro s inner out out' h h'
  exact h.trans h'.symm

/-- Every completed modeled execution of the actual source body has the
mathematically correct result. This strengthens the forward existence theorem
without adding an output premise or trusting an alternate execution. -/
theorem count_function_execution_correct {bound result : Nat} {heap : Heap} {t : State}
    (word : bound<wordMod)
    (run : Run service (stmt Source.countFunction.body) (countInput bound heap)
      (.returned t result)) : result=Nat.primeCounting bound ∧ t.heap=heap := by
  obtain ⟨expected,correct,unchanged⟩ :=
    count_function_refines (count_exec_complete bound word) word heap
  have same := stmt_deterministic
    (Eval:=Eval service) (Declare:=Declare service) (truth:=truth) (Scope:=Scope)
    (eval_deterministic service) (declare_deterministic service) scope_deterministic run correct
  cases same
  exact ⟨rfl,unchanged⟩

/-- A source-program output is transported directly into the actual real
Ramanujan consumer. The two completed source executions remain explicit witnesses
until a particular numerical execution/certificate constructs them. -/
theorem source_cell_sound (c : RamanujanPV.Cell)
    (wordP : c.m<wordMod) (wordQ : c.j<wordMod)
    {heapP heapQ : Heap} {stateP stateQ : State}
    (runP : Run service (stmt Source.countFunction.body) (countInput c.m heapP)
      (.returned stateP c.P))
    (runQ : Run service (stmt Source.countFunction.body) (countInput c.j heapQ)
      (.returned stateQ c.Q))
    (predicate : c.FixedPredicate) (enclosures : c.Enclosures)
    {x : ℝ} (hn : (c.n : ℝ) ≤ x) (hm : x < (c.m : ℝ)+1) : RamanujanPV.Holds x := by
  have counts : c.CountsCorrect :=
    ⟨(count_function_execution_correct wordP runP).1.symm,
     (count_function_execution_correct wordQ runQ).1.symm⟩
  exact RamanujanPV.fixed_cell_sound c predicate counts enclosures hn hm

#print axioms source_cell_sound
#print axioms count_function_execution_correct
end RamanujanPV.AST.C
