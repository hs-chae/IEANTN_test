/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTPureDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics PureDeterminism

/-- Pointwise totality and all-order determinism of an actual source segment.
It asserts no mathematical output and supplies no source execution oracle. -/
structure NormalSegment {F : Type} (context : Context F) (before : State F)
    (statements : List Stmt) (after : State F) : Prop where
  execution : ExecList context before statements .normal after
  every : ∀other flow, ExecList context before statements flow other → flow=.normal ∧ other=after

theorem NormalSegment.nil {F : Type} (context : Context F) (state : State F) :
    NormalSegment context state [] state :=
  ⟨.nil,by intro other flow run;cases run;exact ⟨rfl,rfl⟩⟩

theorem NormalSegment.cons {F : Type} {context : Context F} {before middle after : State F}
    {statement : Stmt} {statements : List Stmt}
    (run : Exec context before statement .normal middle)
    (every : ∀other flow, Exec context before statement flow other → flow=.normal ∧ other=middle)
    (tail : NormalSegment context middle statements after) :
    NormalSegment context before (statement::statements) after := by
  refine ⟨.cons run tail.execution,?_⟩
  intro other flow actual
  cases actual with
  | cons head rest =>
    obtain ⟨_,rfl⟩ := every _ _ head
    exact tail.every _ _ rest
  | abrupt head impossible => exact False.elim (impossible (every _ _ head).1)

theorem NormalSegment.single {F : Type} {context : Context F} {before after : State F} {statement : Stmt}
    (run : Exec context before statement .normal after)
    (every : ∀other flow, Exec context before statement flow other → flow=.normal ∧ other=after) :
    NormalSegment context before [statement] after :=
  .cons run every (.nil context after)

private theorem append_execution {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} {flow : Flow}
    (first : ExecList context before xs .normal middle) (second : ExecList context middle ys flow after) :
    ExecList context before (xs++ys) flow after := by
  induction xs generalizing before with
  | nil => cases first;exact second
  | cons s ss ih =>
    cases first with
    | cons head tail => exact .cons head (ih tail)
    | abrupt head impossible => exact False.elim (impossible rfl)

private theorem split_execution {F : Type} {context : Context F} {before after : State F}
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

theorem NormalSegment.append {F : Type} {context : Context F} {before middle after : State F}
    {xs ys : List Stmt} (first : NormalSegment context before xs middle)
    (second : NormalSegment context middle ys after) : NormalSegment context before (xs++ys) after := by
  refine ⟨append_execution first.execution second.execution,?_⟩
  intro other flow run
  rcases split_execution run with ⟨current,initialRun,suffix⟩ | ⟨abrupt,initialRun⟩
  · obtain ⟨_,rfl⟩ := first.every _ _ initialRun
    exact second.every _ _ suffix
  · exact False.elim (abrupt (first.every _ _ initialRun).1)

/-- Determinism is proved from actual pure source instructions and their real
execution; no certificate result or initialized application state is assumed. -/
theorem NormalSegment.pure {F : Type} {context : Context F} {before after : State F}
    {statements : List Stmt} (run : ExecList context before statements .normal after)
    (simple : ∀s∈statements,Simple s) : NormalSegment context before statements after := by
  induction statements generalizing before with
  | nil => cases run;exact .nil context after
  | cons s ss ih =>
    cases run with
    | cons head tail =>
      apply NormalSegment.cons head _ (ih tail (by intro s hs;exact simple s (by simp [hs])))
      intro other flow actual
      obtain ⟨same,states⟩ := simple_unique (simple s (by simp)) head actual
      exact ⟨same.symm,states.symm⟩
    | abrupt head impossible => exact False.elim (impossible rfl)

#print axioms NormalSegment.append
#print axioms NormalSegment.pure
end RH080Next.FFTPV.RecursiveSource
