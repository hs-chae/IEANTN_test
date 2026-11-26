/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLoopTotal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceBindings PureDeterminism

structure ResultSegment {F : Type} (context : Context F) (before : State F)
    (statements : List Stmt) (flow : Flow) (after : State F) : Prop where
  execution : ExecList context before statements flow after
  every : ∀other actual,ExecList context before statements actual other → actual=flow ∧ other=after

private theorem result_append_execution {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow}
    (first : ExecList context before xs .normal middle) (second : ExecList context middle ys flow after) :
    ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil => cases first;exact second
  | cons s ss ih =>
    cases first with
    | cons head tail => exact .cons head (ih tail)
    | abrupt head impossible => exact False.elim (impossible rfl)

private theorem result_split_execution {F : Type} {context : Context F} {before after : State F}
    {xs ys : List Stmt} {flow : Flow} (run : ExecList context before (xs++ys) flow after) :
    (∃middle,ExecList context before xs .normal middle ∧ ExecList context middle ys flow after) ∨
      (flow≠.normal ∧ ExecList context before xs flow after) := by
  induction xs generalizing before with
  | nil => exact Or.inl ⟨before,.nil,run⟩
  | cons s ss ih =>
    cases run with
    | cons head tail =>
      rcases ih tail with ⟨middle,initialRun,suffix⟩ | ⟨abrupt,initialRun⟩
      · exact Or.inl ⟨middle,.cons head initialRun,suffix⟩
      · exact Or.inr ⟨abrupt,.cons head initialRun⟩
    | abrupt head impossible => exact Or.inr ⟨impossible,.abrupt head impossible⟩

/-- Compose a complete actual normal prefix with a fixed abrupt suffix,
preserving all permitted executions of both full lists. -/
theorem NormalSegment.then_result {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow} (head : NormalSegment context before xs middle)
    (tail : ResultSegment context middle ys flow after) : ResultSegment context before (xs++ys) flow after := by
  refine ⟨result_append_execution head.execution tail.execution,?_⟩
  intro other actual actualRun
  rcases result_split_execution actualRun with ⟨current,initialRun,suffix⟩ | ⟨abrupt,initialRun⟩
  · obtain ⟨_,rfl⟩:=head.every _ _ initialRun
    exact tail.every _ _ suffix
  · exact False.elim (abrupt (head.every _ _ initialRun).1)

/-- The actual final return reads the source status slot, whose value is the
success result established by the two actual recursive calls. -/
theorem LoopView.final_return {F : Type} (context : Context F) {state : State F}
    {total : Nat} {buffers : Buffers total} {start index step n owner j : Nat}
    {ids : LoopVar → Nat} {input table output work : Nat → Nat}
    (h : LoopView state buffers start index step n ids owner j input table output work) :
    ResultSegment context state [finalReturn] (.returned (.integer (integer64 0))) state := by
  have evaluated : Eval context state (.variable "status") (.integer (integer64 0)) state :=
    .variable (h.bindings.lookup (.inr .status)) (h.bindings.read (.inr .status))
  have run : Exec context state finalReturn (.returned (.integer (integer64 0))) state := .returnSome evaluated
  refine ⟨.abrupt run (by intro bad;cases bad),?_⟩
  intro other actual actualRun
  cases actualRun with
  | cons first rest =>
    have impossible:=(simple_unique (by trivial) run first).1
    cases impossible
  | abrupt first impossible =>
    obtain ⟨same,states⟩:=simple_unique (by trivial) run first
    exact ⟨same.symm,states.symm⟩

#print axioms NormalSegment.then_result
#print axioms LoopView.final_return
end RH080Next.FFTPV.RecursiveSource
