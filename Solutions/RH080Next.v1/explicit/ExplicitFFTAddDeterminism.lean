/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays

theorem simple_unique {F : Type} (context : Context F) (stmt : Stmt) (simple : PureDeterminism.Simple stmt) :
    CompareSource.Unique context stmt:=fun first second=>PureDeterminism.simple_unique simple first second

theorem add_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context addLoop := by
  apply CompareSource.while_unique (by simp [condition,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  all_goals
    exact simple_unique context _ (by simp [PureDeterminism.Simple,SourcePure.CallFree,addTExpr,digitStmt,carryStmt,carryExpr,advanceStmt])

theorem swap_unique {F : Type} (context : Context F) : CompareSource.Unique context swapBranch := by
  apply DivideSource.if_unique cmpTest _ (by simp [cmpTest,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl
  all_goals exact simple_unique context _ (by simp [PureDeterminism.Simple,SourcePure.CallFree])

theorem sub_loop_unique {F : Type} (context : Context F) : CompareSource.Unique context subLoop := by
  apply CompareSource.while_unique (by simp [condition,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact simple_unique context _ (by simp [PureDeterminism.Simple,SourcePure.CallFree])
  · exact simple_unique context _ (by simp [PureDeterminism.Simple,SourcePure.CallFree])
  · exact swap_unique context
  all_goals
    exact simple_unique context _ (by simp [PureDeterminism.Simple,SourcePure.CallFree,subTExpr,digitStmt,carryStmt,carryExpr,advanceStmt])

theorem choose_sign_unique {F : Type} (context : Context F) : CompareSource.Unique context chooseSign := by
  apply DivideSource.if_unique cmpTest _ (by simp [cmpTest,SourcePure.CallFree])
  apply CompareSource.block_unique
  intro stmt member
  simp only [List.mem_singleton] at member
  subst stmt
  exact simple_unique context _ (by simp [PureDeterminism.Simple,SourcePure.CallFree])

theorem arithmetic_unique {F : Type} (context : Context F) : CompareSource.Unique context arithmeticBranch := by
  have yes : CompareSource.Unique context additionBranch:=by
    apply CompareSource.block_unique
    intro stmt member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl|rfl
    · exact add_loop_unique context
    · exact simple_unique context _ (by simp [storeSign,PureDeterminism.Simple,SourcePure.CallFree])
  have no : CompareSource.Unique context subtractionBranch:=by
    apply CompareSource.block_unique
    intro stmt member
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl
    · exact simple_unique context _ (by simp [signDeclaration,PureDeterminism.Simple,SourcePure.CallFree])
    · exact choose_sign_unique context
    · exact sub_loop_unique context
    · exact simple_unique context _ (by simp [storeSign,PureDeterminism.Simple,SourcePure.CallFree])
    · exact simple_unique context _ (by simp [clearCarry,PureDeterminism.Simple,SourcePure.CallFree])
  intro before a b fa fb first second
  cases first with
  | ifTrue ev tr run=>
    cases second with
    | ifTrue ev' tr' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by simp [sameSignTest,SourcePure.CallFree]) ev ev'
      exact yes run run'
    | ifElse ev' tr' run'=>
      cases (PureDeterminism.eval_unique (by simp [sameSignTest,SourcePure.CallFree]) ev ev').1
      simp_all
  | ifElse ev tr run=>
    cases second with
    | ifTrue ev' tr' run'=>
      cases (PureDeterminism.eval_unique (by simp [sameSignTest,SourcePure.CallFree]) ev ev').1
      simp_all
    | ifElse ev' tr' run'=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by simp [sameSignTest,SourcePure.CallFree]) ev ev'
      exact no run run'

theorem function_statements_unique {F : Type} (context : Context F)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast) :
    ∀s∈functionStatements,CompareSource.Unique context s := by
  intro stmt member
  simp only [functionStatements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact simple_unique context _ (by simp [asDeclaration,PureDeterminism.Simple,SourcePure.CallFree])
  · exact simple_unique context _ (by simp [bsDeclaration,PureDeterminism.Simple,SourcePure.CallFree])
  · apply DivideSource.if_unique flipTest _ (by simp [flipTest,SourcePure.CallFree])
    apply CompareSource.block_unique
    intro stmt member
    simp only [List.mem_singleton] at member
    subst stmt
    exact simple_unique context _ (by simp [flipSign,PureDeterminism.Simple,SourcePure.CallFree])
  · exact simple_unique context _ (by simp [jDeclaration,PureDeterminism.Simple,SourcePure.CallFree])
  · exact simple_unique context _ (by simp [carryDeclaration,PureDeterminism.Simple,SourcePure.CallFree])
  · exact ApplicationPureCall.declare_call_unique "magnitude_compare" [.variable "a",.variable "b"]
      (by simp [SourcePure.CallFree]) .u64 "cmp" (CompareSource.returned_call_unique compareSelected)
  · exact arithmetic_unique context
  · exact ApplicationPureCall.expression_call_unique "canonical_sign" [.variable "out"]
      (by simp [SourcePure.CallFree]) (CanonicalSource.call_unique canonicalSelected)
  · exact simple_unique context _ (by simp [returnStatement,PureDeterminism.Simple,SourcePure.CallFree])

theorem function_body_unique {F : Type} {context : Context F}
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before a b : State F} {fa fb : Flow}
    (first : Body context functionStatements before functionStatements fa a)
    (second : Body context functionStatements before functionStatements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _=>
    cases second with
    | finish run' _=>exact CompareSource.list_unique (function_statements_unique context compareSelected canonicalSelected) run run'
    | jump run' target tail=>simp [functionStatements,asDeclaration,bsDeclaration,flipBranch,jDeclaration,carryDeclaration,
        cmpDeclaration,arithmeticBranch,canonicalStatement,returnStatement,labelTail] at target
  | jump run target tail=>simp [functionStatements,asDeclaration,bsDeclaration,flipBranch,jDeclaration,carryDeclaration,
      cmpDeclaration,arithmeticBranch,canonicalStatement,returnStatement,labelTail] at target

theorem returned_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonicalSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "fixed_add" args before (.value value) a)
    (second : Call context "fixed_add" args before result b) : result=.value value ∧ b=a := by
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
      obtain ⟨flowEq,middleEq⟩:=function_body_unique compareSelected canonicalSelected bodyA bodyB
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
      cases (function_body_unique compareSelected canonicalSelected bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

#print axioms arithmetic_unique
#print axioms function_body_unique
#print axioms returned_call_unique
end RH080Next.FFTPV.AddSource
