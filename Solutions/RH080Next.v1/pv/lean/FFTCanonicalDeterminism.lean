/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCanonicalCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CanonicalSource
open GoldbachDirect GoldbachDirect.Semantics

/-- Unrestricted actual Call determinism, including termination alternatives.
No application array precondition is needed for this uniqueness theorem. -/
theorem call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before a b : State F} {args : List Value} {ra rb : CallResult}
    (first : Call context "canonical_sign" args before ra a)
    (second : Call context "canonical_sign" args before rb b) : rb=ra ∧ b=a := by
  cases first with
  | external absent named foreign => rw [selected] at absent;cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA =>
    exact returned_call_unique selected (.internal selectedA shapeA paramsA bodyA convertA finishA) second
  | internalVoid selectedA shapeA void paramsA bodyA finishA =>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void
  | internalTerminated selectedA shapeA paramsA bodyA =>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign => rw [selected] at absent;cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB =>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (function_body_unique bodyA bodyB).1
    | internalVoid selectedB shapeB void paramsB bodyB finishB =>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB =>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq,middleEq⟩:=function_body_unique bodyA bodyB
      cases flowEq
      cases middleEq
      exact ⟨rfl,rfl⟩

#print axioms call_unique
end RH080Next.FFTPV.CanonicalSource
