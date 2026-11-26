/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachDirect.SourcePure
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.BlockEnvironment
open GoldbachDirect GoldbachDirect.Semantics

/-- Lexical block exit restores the complete original source environment.
This says nothing about stored values or heap effects of the block. -/
theorem block_environment {F : Type} {context : Context F} {before after : State F}
    {statements : List Stmt} {flow : Flow}
    (run : Exec context before (.block statements) flow after) : after.environment=before.environment := by
  cases run with
  | block entered body finished=>subst_vars;rfl

def ClosedScope : Stmt → Prop
  | .block _=>True
  | .whileLoop condition body=>SourcePure.CallFree condition ∧ ∃statements,body=.block statements
  | _=>False

/-- A general proof over the actual finite execution derivation. Calls inside
blocks need not be pure or have favorable results: actual lexical scope exit
restores bindings, while a call-free while condition changes no state. -/
theorem closed_scope_environment {F : Type} {context : Context F}
    {before after : State F} {statement : Stmt} {flow : Flow}
    (run : Exec context before statement flow after) :
    ClosedScope statement → after.environment=before.environment := by
  apply Exec.rec
    (motive_1:=fun _ _ _ _ _=>True)
    (motive_2:=fun _ _ _ _ _=>True)
    (motive_3:=fun _ _ _ _ _=>True)
    (motive_4:=fun _ _ _ _ _=>True)
    (motive_5:=fun before statement _ after _=>ClosedScope statement → after.environment=before.environment)
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
    exact congrArg State.environment (SourcePure.eval_state evaluated only.1)
  case whileNext=>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (restIH only).trans ((block_environment bodyRun).trans
      (congrArg State.environment (SourcePure.eval_state evaluated only.1)))
  case whileContinue=>
    intro before condition value tested body middle flow after evaluated truth bodyRun rest _ bodyIH restIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (restIH only).trans ((block_environment bodyRun).trans
      (congrArg State.environment (SourcePure.eval_state evaluated only.1)))
  case whileBreak=>
    intro before condition value tested body after evaluated truth bodyRun _ bodyIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (block_environment bodyRun).trans (congrArg State.environment (SourcePure.eval_state evaluated only.1))
  case whileExit=>
    intro before condition value tested body flow after evaluated truth bodyRun abrupt _ bodyIH only
    obtain ⟨statements,eq⟩:=only.2
    subst body
    exact (block_environment bodyRun).trans (congrArg State.environment (SourcePure.eval_state evaluated only.1))
  all_goals intros;simp_all only [ClosedScope]

theorem while_block_environment {F : Type} {context : Context F} {before after : State F}
    {condition : Expr} {statements : List Stmt} {flow : Flow}
    (pureCondition : SourcePure.CallFree condition)
    (run : Exec context before (.whileLoop condition (.block statements)) flow after) :
    after.environment=before.environment :=
  closed_scope_environment run ⟨pureCondition,statements,rfl⟩

#print axioms block_environment
#print axioms while_block_environment
end RH080Next.FFTPV.BlockEnvironment
