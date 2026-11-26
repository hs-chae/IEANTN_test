/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopyEveryCall
import ExplicitFFTCompareDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CopyLoop
open GoldbachDirect GoldbachDirect.Semantics
open CompareSource (Unique list_unique block_unique while_unique)

theorem copy_body_actual : copy_words_ast.body=.block functionStatements := iterative_body_actual

theorem copy_loop_body_unique {F : Type} (context : Context F) : Unique context loopBody := by
  apply block_unique
  intro stmt member
  simp only [loopBody,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [storeStmt,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [increment,ZeroLoop.increment,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem copy_loop_unique {F : Type} (context : Context F) : Unique context loop :=
  while_unique (by simp [condition,ZeroLoop.condition,SourcePure.CallFree]) (copy_loop_body_unique context)

theorem function_statements_unique {F : Type} (context : Context F) :
    ∀s∈functionStatements,Unique context s := by
  intro stmt member
  simp only [functionStatements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [localDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact copy_loop_unique context
  · exact fun first second => PureDeterminism.simple_unique
      (by simp [zeroReturn,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem function_body_unique {F : Type} {context : Context F}
    {before a b : State F} {fa fb : Flow}
    (first : Body context functionStatements before functionStatements fa a)
    (second : Body context functionStatements before functionStatements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _ =>
    cases second with
    | finish run' _ => exact list_unique (function_statements_unique context) run run'
    | jump run' target tail => simp [functionStatements,localDeclaration,loop,zeroReturn,labelTail] at target
  | jump run target tail => simp [functionStatements,localDeclaration,loop,zeroReturn,labelTail] at target

/-- Every full Call has the same return and resulting caller state as the
constructed terminating execution. This discharges universal correctness;
no favorable-trace interpretation is used. -/
theorem call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "copy_words"=some copy_words_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "copy_words" args before (.value value) a)
    (second : Call context "copy_words" args before result b) :
    result=.value value ∧ b=a := by
  cases first with
  | external absent named foreign => rw [selected] at absent; cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements=_ := Stmt.block.inj (copy_body_actual.symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign => rw [selected] at absent; cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_ := Stmt.block.inj (copy_body_actual.symm.trans shapeB)
      subst_vars
      have enteredEq := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq,middleEq⟩ := function_body_unique bodyA bodyB
      cases flowEq
      cases middleEq
      have valueEq := Option.some.inj (convertA.symm.trans convertB)
      cases valueEq
      exact ⟨rfl,rfl⟩
    | internalVoid selectedB shapeB void paramsB bodyB finishB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB =>
      have functionB := Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_ := Stmt.block.inj (copy_body_actual.symm.trans shapeB)
      subst_vars
      have enteredEq := Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (function_body_unique bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA =>
    have functionA := Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

#print axioms copy_loop_unique
#print axioms function_body_unique
#print axioms call_unique
end RH080Next.FFTPV.CopyLoop
