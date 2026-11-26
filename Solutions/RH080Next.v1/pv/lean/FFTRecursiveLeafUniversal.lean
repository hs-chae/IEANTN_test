/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLeafDeterminism
import FFTRecursiveLeafSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays PureDeterminism
open SourceLocals SourceScalarSlots SourceBindings

private theorem leaf_returned_value {F : Type} {context : Context F}
    {before after : State F} {value : Value}
    (test : Eval context before leafCondition (.integer (.boolean true)) before)
    (run : Body context functionStatements before functionStatements (.returned value) after) :
    value = .integer (integer64 0) := by
  have noLabel : ∀label, labelTail label functionStatements = none := by intro label;rfl
  cases run with
  | jump run target tail => rw [noLabel] at target;cases target
  | finish run noJump =>
    rw [actual_leaf_head] at run
    cases run with
    | cons first rest => exact False.elim (leaf_branch_not_normal test first)
    | abrupt first abrupt =>
      cases first with
      | ifTrue evaluated truth body =>
        cases body with
        | block entered body finished =>
          cases body with
          | cons first rest =>
            cases rest with
            | cons returned rest => cases returned
            | abrupt returned abrupt =>
              cases returned with
              | returnSome evaluated =>
                obtain ⟨same,_⟩ := eval_unique (by trivial)
                  (Eval.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) evaluated
                exact same.symm
          | abrupt first abrupt => cases first

/-- Every full source Call agrees with a known terminating actual leaf Call,
including all operand/argument orders and the terminated-call alternative. -/
theorem leaf_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "fft_recursive" = some FFTRecursivePV.fft_recursive_ast)
    (copySelected : findFunction context.program "copy_words" = some FFTRecursivePV.copy_words_ast)
    {caller a b : State F} {outObj inObj twiddleObj workObj start index step total : Nat}
    (well : WellScoped caller) (startFit : start < 2^64) (indexFit : index < 2^64)
    (stepFit : step < 2^64) (totalFit : total < 2^64) {result : CallResult}
    (first : Call context "fft_recursive"
      (arguments outObj inObj twiddleObj workObj start index step 1 total)
      caller (.value (.integer (integer64 0))) a)
    (second : Call context "fft_recursive"
      (arguments outObj inObj twiddleObj workObj start index step 1 total) caller result b) :
    result = .value (.integer (integer64 0)) ∧ b = a := by
  let entry : State F := {caller.enterScope with environment := []}
  have we : WellScoped entry := wellScoped_environment (wellScoped_enter well) []
  obtain ⟨entered,bound,params,chain,pwell,pno,pscope,pns⟩ := initialize_parameters
    outObj inObj twiddleObj workObj start index step 1 total we rfl
    startFit indexFit stepFit (by norm_num) totalFit
  have test : Eval context entered leafCondition (.integer (.boolean true)) entered := by
    refine .binaryLR (Eval.variable (params.lookup .n) (params.read .n))
      (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) ?_
    rfl
  cases first with
  | external absent named foreign => rw [selected] at absent;cases absent
  | internal selectedA shapeA paramsA bodyA convertedA finishedA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements = _ := Stmt.block.inj (actual_body.symm.trans shapeA)
    subst_vars
    have enteredA := Option.some.inj (bound.symm.trans paramsA)
    subst_vars
    have valueA := leaf_returned_value test bodyA
    subst_vars
    cases second with
    | external absent named foreign => rw [selected] at absent;cases absent
    | internal selectedB shapeB paramsB bodyB convertedB finishedB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements = _ := Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredB := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨same,rfl⟩ := leaf_body_unique copySelected test bodyA bodyB
      cases same
      have valueB := Option.some.inj (convertedB.symm.trans (convert64 0 (by norm_num)))
      subst_vars
      exact ⟨rfl,rfl⟩
    | internalVoid selectedB shapeB void paramsB bodyB finishedB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements = _ := Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredB := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (leaf_body_unique copySelected test bodyA bodyB).1

#print axioms leaf_call_unique
end RH080Next.FFTPV.RecursiveSource
