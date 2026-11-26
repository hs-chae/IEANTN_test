/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTCompareDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ApplicationLoopScope
open GoldbachDirect GoldbachDirect.Semantics

theorem block_fields {F : Type} {context : Context F} {before after : State F}
    {body : List Stmt} {flow : Flow} (run : Exec context before (.block body) flow after) :
    after.environment=before.environment ∧ after.scope=before.scope := by
  cases run with | block entered bodyRun finished=>subst_vars; exact ⟨rfl,rfl⟩

theorem while_block_fields_aux {F : Type} {context : Context F} {before after : State F} {stmt : Stmt} {flow : Flow}
    (run : Exec context before stmt flow after) :
    ∀condition body,stmt=.whileLoop condition (.block body) → SourcePure.CallFree condition →
      after.environment=before.environment ∧ after.scope=before.scope := by
  apply Exec.rec
    (motive_1:=fun _ _ _ _ _=>True)
    (motive_2:=fun _ _ _ _ _=>True)
    (motive_3:=fun _ _ _ _ _=>True)
    (motive_4:=fun _ _ _ _ _=>True)
    (motive_5:=fun before stmt flow after _=>
      ∀condition body,stmt=.whileLoop condition (.block body) → SourcePure.CallFree condition →
        after.environment=before.environment ∧ after.scope=before.scope)
    (motive_6:=fun _ _ _ _ _=>True)
    (motive_7:=fun _ _ _ _ _ _=>True)
    (motive_8:=fun _ _ _ _ _ _=>True) (t:=run)
  all_goals try solve | intros; trivial | intros; contradiction
  case whileFalse=>
    intro before actualCondition value after actualBody ev tr _ condition body equality pure
    cases equality
    have same:=SourcePure.eval_state ev pure
    subst after
    exact ⟨rfl,rfl⟩
  case whileNext=>
    intro before actualCondition value tested actualBody middle flow after ev tr first rest _ bodyIH restIH condition body equality pure
    cases equality
    have same:=SourcePure.eval_state ev pure
    subst tested
    obtain ⟨env,scope⟩:=block_fields first
    obtain ⟨env',scope'⟩:=restIH _ _ rfl pure
    exact ⟨env'.trans env,scope'.trans scope⟩
  case whileContinue=>
    intro before actualCondition value tested actualBody middle flow after ev tr first rest _ bodyIH restIH condition body equality pure
    cases equality
    have same:=SourcePure.eval_state ev pure
    subst tested
    obtain ⟨env,scope⟩:=block_fields first
    obtain ⟨env',scope'⟩:=restIH _ _ rfl pure
    exact ⟨env'.trans env,scope'.trans scope⟩
  case whileBreak=>
    intro before actualCondition value tested actualBody after ev tr first _ bodyIH condition body equality pure
    cases equality
    have same:=SourcePure.eval_state ev pure
    subst tested
    exact block_fields first
  case whileExit=>
    intro before actualCondition value tested actualBody flow after ev tr first abrupt _ bodyIH condition body equality pure
    cases equality
    have same:=SourcePure.eval_state ev pure
    subst tested
    exact block_fields first

theorem while_block_fields {F : Type} {context : Context F} {before after : State F}
    {condition : Expr} {body : List Stmt} {flow : Flow}
    (run : Exec context before (.whileLoop condition (.block body)) flow after)
    (pure : SourcePure.CallFree condition) :
    after.environment=before.environment ∧ after.scope=before.scope :=
  while_block_fields_aux run condition body rfl pure

#print axioms while_block_fields
end RH080Next.FFTPV.ApplicationLoopScope
