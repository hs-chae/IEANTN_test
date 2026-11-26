/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTBlockWhileEnvironment
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.BlockEnvironment
open GoldbachDirect GoldbachDirect.Semantics

/-- Lexical block exit restores the actual enclosing source scope.
This says nothing about stored values or heap effects of the block. -/
theorem block_scope {F : Type} {context : Context F} {before after : State F}
    {statements : List Stmt} {flow : Flow}
    (run : Exec context before (.block statements) flow after) : after.scope=before.scope := by
  cases run with
  | block entered body finished=>subst_vars;rfl

/-- A general proof over the actual finite execution derivation. Calls inside
blocks need not be pure or have favorable results: actual lexical scope exit
restores the actual enclosing scope, while a call-free while condition changes no state. -/
theorem closed_scope_state {F : Type} {context : Context F}
    {before after : State F} {statement : Stmt} {flow : Flow}
    (run : Exec context before statement flow after) :
    ClosedScope statement → after.scope=before.scope := by
  apply Exec.rec
    (motive_1:=fun _ _ _ _ _=>True)
    (motive_2:=fun _ _ _ _ _=>True)
    (motive_3:=fun _ _ _ _ _=>True)
    (motive_4:=fun _ _ _ _ _=>True)
    (motive_5:=fun before statement _ after _=>ClosedScope statement → after.scope=before.scope)
    (motive_6:=fun _ _ _ _ _=>True)
    (motive_7:=fun _ _ _ _ _ _=>True)
    (motive_8:=fun _ _ _ _ _ _=>True) (t:=run)
  all_goals try solve | intros;trivial
  case block=>
    intro start body flow middle after before entered bodyRun finished ih _
    subst_vars
    rfl
  case whileFalse=>
    intro before condition value after body evaluated truth _ only
    exact congrArg State.scope (SourcePure.eval_state evaluated only.1)
  case whileNext=>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (restIH only).trans ((block_scope bodyRun).trans
      (congrArg State.scope (SourcePure.eval_state evaluated only.1)))
  case whileContinue=>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (restIH only).trans ((block_scope bodyRun).trans
      (congrArg State.scope (SourcePure.eval_state evaluated only.1)))
  case whileBreak=>
    intro before condition value tested body after evaluated truth bodyRun _ bodyIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (block_scope bodyRun).trans (congrArg State.scope (SourcePure.eval_state evaluated only.1))
  case whileExit=>
    intro before condition value tested body flow after evaluated truth bodyRun abrupt _ bodyIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (block_scope bodyRun).trans (congrArg State.scope (SourcePure.eval_state evaluated only.1))
  all_goals intros;simp_all only [ClosedScope]

theorem while_block_scope {F : Type} {context : Context F} {before after : State F}
    {condition : Expr} {statements : List Stmt} {flow : Flow}
    (pureCondition : SourcePure.CallFree condition)
    (run : Exec context before (.whileLoop condition (.block statements)) flow after) :
    after.scope=before.scope :=
  closed_scope_state run ⟨pureCondition,statements,rfl⟩

#print axioms block_scope
#print axioms while_block_scope
end RH080Next.FFTPV.BlockEnvironment
