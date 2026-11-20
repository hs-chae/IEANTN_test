/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCMachine
import LCMSourcePV.ASTDeterminism

/-! Determinism of the actual typed pointer/word source semantics. A verified
execution yields the unique result of every completed run under the same precise
source and machine state; this does not assume a native output or termination. -/
namespace RamanujanPV.QuotientCDeterminism
open QuotientCMachine LCMSourcePV.ASTLoops
set_option autoImplicit false

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

theorem run_unique {call : Service} {body : LCMSourcePV.Witness.C.Stmt}
    {s : State} {out out' : Flow}
    (first : Run call body s out) (second : Run call body s out') : out=out' :=
  stmt_deterministic (eval_deterministic call) (declare_deterministic call)
    scope_deterministic first second

theorem returned_unique {call : Service} {body : LCMSourcePV.Witness.C.Stmt}
    {s t t' : State} {value value' : Value}
    (first : Run call body s (.returned t value))
    (second : Run call body s (.returned t' value')) : t=t' ∧ value=value' := by
  exact Flow.returned.inj (run_unique first second)

#print axioms run_unique
#print axioms returned_unique
end RamanujanPV.QuotientCDeterminism
