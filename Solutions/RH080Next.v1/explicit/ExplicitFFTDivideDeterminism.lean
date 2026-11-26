/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTDivideCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.DivideSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

theorem if_unique {F : Type} {context : Context F} (test : Expr) (body : Stmt)
    (pure : SourcePure.CallFree test) (unique : CompareSource.Unique context body) :
    CompareSource.Unique context (.ite test body none) := by
  intro before a b fa fb first second
  cases first with
  | ifTrue ev tr run=>
    cases second with
    | ifTrue ev' tr' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique pure ev ev'
      exact unique run run'
    | ifFalse ev' tr'=>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
  | ifFalse ev tr=>
    cases second with
    | ifTrue ev' tr' run'=>
      cases (PureDeterminism.eval_unique pure ev ev').1
      simp_all
    | ifFalse ev' tr'=>exact ⟨rfl,(PureDeterminism.eval_unique pure ev ev').2⟩

theorem rounding_unique {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) :
    CompareSource.Unique context roundingStatement := by
  have callUnique : CompareSource.Unique context incrementStatement:=
    ApplicationPureCall.return_call_unique "increment_words" [.variable "a",.variable "n"]
      (by simp [SourcePure.CallFree]) (IncrementSource.returned_call_unique selected)
  have blockCall : CompareSource.Unique context (.block [incrementStatement]) := by
    apply CompareSource.block_unique
    intro stmt member
    simp only [List.mem_singleton] at member
    subst stmt
    exact callUnique
  have inner : CompareSource.Unique context remainderBranch:=
    if_unique remainderTest _ (by simp [remainderTest,SourcePure.CallFree]) blockCall
  apply if_unique ceilingTest _ (by simp [ceilingTest,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_singleton] at member
  subst stmt
  exact inner

theorem function_statements_unique {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) :
    ∀s∈functionStatements,CompareSource.Unique context s := by
  intro stmt member
  simp only [functionStatements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact fun a b=>PureDeterminism.simple_unique (by simp [jDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) a b
  · exact fun a b=>PureDeterminism.simple_unique (by simp [remDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) a b
  · exact actual_loop_unique context
  · exact rounding_unique context selected
  · exact fun a b=>PureDeterminism.simple_unique (by simp [returnStatement,PureDeterminism.Simple,SourcePure.CallFree]) a b

theorem function_body_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    {before a b : State F} {fa fb : Flow}
    (first : Body context functionStatements before functionStatements fa a)
    (second : Body context functionStatements before functionStatements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _=>
    cases second with
    | finish run' _=>exact CompareSource.list_unique (function_statements_unique context selected) run run'
    | jump run' target tail=>simp [functionStatements,jDeclaration,remDeclaration,loop,roundingStatement,returnStatement,labelTail] at target
  | jump run target tail=>simp [functionStatements,jDeclaration,remDeclaration,loop,roundingStatement,returnStatement,labelTail] at target

theorem returned_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "divide_small"=some divide_small_ast)
    (incrementSelected : findFunction context.program "increment_words"=some increment_words_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "divide_small" args before (.value value) a)
    (second : Call context "divide_small" args before result b) : result=.value value ∧ b=a := by
  cases first with
  | external absent named foreign=>rw [selected] at absent; cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeA)
    subst_vars
    cases second with
    | external absent named foreign=>rw [selected] at absent; cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq,middleEq⟩:=function_body_unique incrementSelected bodyA bodyB
      cases flowEq
      cases middleEq
      have valueEq:=Option.some.inj (convertA.symm.trans convertB)
      cases valueEq
      exact ⟨rfl,rfl⟩
    | internalVoid selectedB shapeB void paramsB bodyB finishB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      cases void
    | internalTerminated selectedB shapeB paramsB bodyB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_:=Stmt.block.inj (actual_body.symm.trans shapeB)
      subst_vars
      have enteredEq:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (function_body_unique incrementSelected bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

#print axioms rounding_unique
#print axioms function_body_unique
#print axioms returned_call_unique
end RH080Next.FFTPV.DivideSource
