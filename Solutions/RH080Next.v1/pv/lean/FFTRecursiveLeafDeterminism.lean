/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLeafExpressions
import FFTCopyDeterminism
import ExplicitApplicationPureCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays PureDeterminism

private theorem arguments_closed : ∀e ∈ leafArguments, SourcePure.CallFree e := by
  intro e he
  simp only [leafArguments,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl <;> trivial

/-- The actual leaf copy statement is deterministic for every source operand
order, including exclusion of a spurious terminated Call alternative. -/
theorem leaf_copy_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "copy_words" = some FFTRecursivePV.copy_words_ast)
    {before a b : State F} {flow : Flow}
    (first : Exec context before leafCopy .normal a)
    (second : Exec context before leafCopy flow b) : flow = .normal ∧ b = a := by
  change Exec context before (.expression (.call "copy_words" leafArguments)) .normal a at first
  change Exec context before (.expression (.call "copy_words" leafArguments)) flow b at second
  cases first with
  | expression first =>
    cases first with
    | load place read => cases place
    | call argsA callA =>
      cases second with
      | expression second =>
        cases second with
        | load place read => cases place
        | call argsB callB =>
          obtain ⟨rfl,rfl,rfl⟩ := ApplicationPureCall.args_unique arguments_closed argsA argsB
          obtain ⟨_,rfl⟩ := CopyLoop.call_unique selected callA callB
          exact ⟨rfl,rfl⟩
      | callTerminated argsB callB =>
        obtain ⟨rfl,rfl,rfl⟩ := ApplicationPureCall.args_unique arguments_closed argsA argsB
        cases (CopyLoop.call_unique selected callA callB).1

private theorem zero_return_unique {F : Type} {context : Context F}
    {before a b : State F} {fa fb : Flow}
    (first : Exec context before zeroReturn fa a)
    (second : Exec context before zeroReturn fb b) : fa = fb ∧ a = b :=
  simple_unique (by trivial) first second

private theorem copy_return_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "copy_words" = some FFTRecursivePV.copy_words_ast)
    {before a b : State F} {flow : Flow}
    (first : ExecList context before [leafCopy,zeroReturn] (.returned (.integer (integer64 0))) a)
    (second : ExecList context before [leafCopy,zeroReturn] flow b) :
    flow = .returned (.integer (integer64 0)) ∧ b = a := by
  cases first with
  | cons copyA tailA =>
    cases tailA with
    | cons returnA tailA => cases returnA
    | abrupt returnA abruptA =>
      cases second with
      | cons copyB tailB =>
        obtain ⟨_,rfl⟩ := leaf_copy_unique selected copyA copyB
        cases tailB with
        | cons returnB tailB => cases returnB
        | abrupt returnB abruptB =>
          obtain ⟨same,rfl⟩ := zero_return_unique returnA returnB
          exact ⟨same.symm,rfl⟩
      | abrupt copyB abruptB =>
        exact False.elim (abruptB (leaf_copy_unique selected copyA copyB).1)
  | abrupt copyA abruptA => cases copyA

private theorem leaf_block_returned_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "copy_words" = some FFTRecursivePV.copy_words_ast)
    {before a b : State F} {flow : Flow}
    (first : Exec context before (.block [leafCopy,zeroReturn]) (.returned (.integer (integer64 0))) a)
    (second : Exec context before (.block [leafCopy,zeroReturn]) flow b) :
    flow = .returned (.integer (integer64 0)) ∧ b = a := by
  cases first with
  | block enterA bodyA finishA =>
    cases second with
    | block enterB bodyB finishB =>
      subst_vars
      obtain ⟨same,rfl⟩ := copy_return_unique selected bodyA bodyB
      exact ⟨same,rfl⟩

/-- Every run of the actual n=1 branch matches the actual known returned run. -/
theorem leaf_branch_returned_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "copy_words" = some FFTRecursivePV.copy_words_ast)
    {before a b : State F} {flow : Flow}
    (first : Exec context before leafBranch (.returned (.integer (integer64 0))) a)
    (second : Exec context before leafBranch flow b) :
    flow = .returned (.integer (integer64 0)) ∧ b = a := by
  cases first with
  | ifTrue testA truthA bodyA =>
    cases second with
    | ifTrue testB truthB bodyB =>
      obtain ⟨rfl,rfl⟩ := eval_unique (by trivial) testA testB
      exact leaf_block_returned_unique selected bodyA bodyB
    | ifFalse testB truthB =>
      obtain ⟨rfl,rfl⟩ := eval_unique (by trivial) testA testB
      rw [truthA] at truthB
      cases truthB

/-- The explicit return at the end of the leaf block rules out falling through
into recursive source statements when n=1. -/
theorem leaf_branch_not_normal {F : Type} {context : Context F} {before after : State F}
    (test : Eval context before leafCondition (.integer (.boolean true)) before)
    (run : Exec context before leafBranch .normal after) : False := by
  cases run with
  | ifTrue testB truthB bodyB =>
    obtain ⟨rfl,rfl⟩ := eval_unique (by trivial) test testB
    cases bodyB with
    | block entered body finished =>
      cases body with
      | cons first rest =>
        cases rest with
        | cons returned rest => cases returned
        | abrupt returned impossible => exact impossible rfl
      | abrupt first impossible => exact impossible rfl
  | ifFalse testB truthB =>
    obtain ⟨rfl,rfl⟩ := eval_unique (by trivial) test testB
    cases truthB

/-- Actual full function-body uniqueness restricted to its proved n=1 domain.
The rest of the source is unreachable by the proved explicit return. -/
theorem leaf_body_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "copy_words" = some FFTRecursivePV.copy_words_ast)
    {before a b : State F} {flow : Flow}
    (test : Eval context before leafCondition (.integer (.boolean true)) before)
    (first : Body context functionStatements before functionStatements (.returned (.integer (integer64 0))) a)
    (second : Body context functionStatements before functionStatements flow b) :
    flow = .returned (.integer (integer64 0)) ∧ b = a := by
  have noLabel : ∀label, labelTail label functionStatements = none := by intro label;rfl
  cases first with
  | jump run target tail => rw [noLabel] at target;cases target
  | finish first noJumpA =>
    rw [actual_leaf_head] at first
    cases first with
    | cons head rest => exact False.elim (leaf_branch_not_normal test head)
    | abrupt headA abruptA =>
      cases second with
      | jump run target tail => rw [noLabel] at target;cases target
      | finish second noJumpB =>
        rw [actual_leaf_head] at second
        cases second with
        | cons head rest => exact False.elim (leaf_branch_not_normal test head)
        | abrupt headB abruptB => exact leaf_branch_returned_unique selected headA headB

#print axioms leaf_body_unique
end RH080Next.FFTPV.RecursiveSource
