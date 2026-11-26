/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyCall
import FFTFixedMultiplyPrefixUnique
import FFTFixedMultiplySuffixUniversal
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyCall
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def functionStatements : List Stmt := ProductRow.items fixed_multiply_ast.body

theorem body_unique_at_core {F : Type} {context : Context F}
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    {entered current a b : State F} {fa fb : Flow}
    (known : ExecList context entered [MultiplyParameters.zeroCall,MultiplyParameters.iDeclaration,ProductOuter.outerLoop] .normal current)
    (unique : ∀{x y : State F}{fx fy : Flow},
      ExecList context current MultiplySuffix.statements fx x →
      ExecList context current MultiplySuffix.statements fy y → fx=fy ∧ x=y)
    (first : Body context functionStatements entered functionStatements fa a)
    (second : Body context functionStatements entered functionStatements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _=>
    cases second with
    | finish run' _=>
      have shape : functionStatements=[MultiplyParameters.zeroCall,MultiplyParameters.iDeclaration,ProductOuter.outerLoop]++MultiplySuffix.statements:=by rfl
      rw [shape] at run run'
      exact unique (consume_initialized_prefix zeroSelected known run) (consume_initialized_prefix zeroSelected known run')
    | jump run' target tail=>simp [functionStatements,ProductRow.items,fixed_multiply_ast,labelTail] at target
  | jump run target tail=>simp [functionStatements,ProductRow.items,fixed_multiply_ast,labelTail] at target

theorem returned_call_unique_at {F : Type} {context : Context F}
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    {before entered a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (params : bindParameters {before.enterScope with environment:=[]} fixed_multiply_ast.parameters args=some entered)
    (unique : ∀{x y : State F}{fx fy : Flow},
      Body context functionStatements entered functionStatements fx x →
      Body context functionStatements entered functionStatements fy y → fx=fy ∧ x=y)
    (first : Call context "fixed_multiply" args before (.value value) a)
    (second : Call context "fixed_multiply" args before result b) : result=.value value ∧ b=a := by
  cases first with
  | external absent named foreign=>rw [selected] at absent;cases absent
  | internal selectedA shapeA paramsA bodyA convertA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    have statementsA : functionStatements=_:=Stmt.block.inj shapeA
    subst_vars
    have entryA:=Option.some.inj (params.symm.trans paramsA)
    subst_vars
    cases second with
    | external absent named foreign=>rw [selected] at absent;cases absent
    | internal selectedB shapeB paramsB bodyB convertB finishB=>
      have functionB:=Option.some.inj (selected.symm.trans selectedB)
      subst_vars
      have statementsB : functionStatements=_:=Stmt.block.inj shapeB
      subst_vars
      have entryB:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      obtain ⟨flowEq,middleEq⟩:=unique bodyA bodyB
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
      have statementsB : functionStatements=_:=Stmt.block.inj shapeB
      subst_vars
      have entryB:=Option.some.inj (paramsA.symm.trans paramsB)
      subst_vars
      cases (unique bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

#print axioms body_unique_at_core
#print axioms returned_call_unique_at
end RH080Next.FFTPV.MultiplyCall
