/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveSegments
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics PureDeterminism

theorem NormalSegment.statement {F : Type} {context : Context F} {before after : State F}
    {statement : Stmt} (h : NormalSegment context before [statement] after) :
    Exec context before statement .normal after := by
  cases h.execution with
  | cons head tail => cases tail;exact head
  | abrupt head impossible => exact False.elim (impossible rfl)

theorem NormalSegment.every_statement {F : Type} {context : Context F} {before after other : State F}
    {statement : Stmt} {flow : Flow} (h : NormalSegment context before [statement] after)
    (run : Exec context before statement flow other) : flow=.normal ∧ other=after := by
  by_cases normal : flow=.normal
  · subst flow;exact h.every _ _ (.cons run .nil)
  · exact h.every _ _ (.abrupt run normal)

/-- The real while rules terminate immediately on a pure false test. All
other execution constructors are ruled out by the actual expression semantics. -/
theorem NormalSegment.while_false {F : Type} {context : Context F} {before : State F}
    {condition : Expr} {body : Stmt} (pure : SourcePure.CallFree condition)
    (test : Eval context before condition (.integer (.boolean false)) before) :
    NormalSegment context before [.whileLoop condition body] before := by
  apply NormalSegment.single (.whileFalse test rfl)
  intro other flow actual
  cases actual with
  | whileFalse tested truth =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    exact ⟨rfl,rfl⟩
  | whileNext tested truth bodyRun rest =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    contradiction
  | whileContinue tested truth bodyRun rest =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    contradiction
  | whileBreak tested truth bodyRun =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    contradiction
  | whileExit tested truth bodyRun abrupt =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    contradiction

/-- One true source test, one total real body and the actual tail while.
The proof excludes continue/break/return/termination, rather than assuming a
restricted loop interpreter or selected source evaluation order. -/
theorem NormalSegment.while_next {F : Type} {context : Context F} {before middle after : State F}
    {condition : Expr} {body : Stmt} (pure : SourcePure.CallFree condition)
    (test : Eval context before condition (.integer (.boolean true)) before)
    (step : NormalSegment context before [body] middle)
    (rest : NormalSegment context middle [.whileLoop condition body] after) :
    NormalSegment context before [.whileLoop condition body] after := by
  apply NormalSegment.single (.whileNext test rfl step.statement rest.statement)
  intro other flow actual
  cases actual with
  | whileFalse tested truth =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    contradiction
  | whileNext tested truth bodyRun tail =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    obtain ⟨_,rfl⟩:=step.every_statement bodyRun
    exact rest.every_statement tail
  | whileContinue tested truth bodyRun tail =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    have impossible:=step.every_statement bodyRun
    cases impossible.1
  | whileBreak tested truth bodyRun =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    have impossible:=step.every_statement bodyRun
    cases impossible.1
  | whileExit tested truth bodyRun abrupt =>
    obtain ⟨rfl,rfl⟩:=eval_unique pure test tested
    exact False.elim (abrupt.1 (step.every_statement bodyRun).1)

#print axioms NormalSegment.while_false
#print axioms NormalSegment.while_next
end RH080Next.FFTPV.RecursiveSource
