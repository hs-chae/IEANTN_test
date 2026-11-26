/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixUniversal
import FFTZeroSliceCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroCallUnique
open GoldbachDirect GoldbachDirect.Semantics WordArrays

def localDeclaration : Stmt:=ZeroSlice.localDeclaration
def zeroReturn : Stmt:=ZeroSlice.zeroReturn
def functionStatements : List Stmt:=[localDeclaration,ZeroLoop.loop,zeroReturn]

theorem actual_body : zero_words_ast.body=.block functionStatements:=by rfl

theorem loop_unique {F : Type} (context : Context F) : CompareSource.Unique context ZeroLoop.loop:=by
  apply CompareSource.while_unique (by simp [ZeroLoop.condition,SourcePure.CallFree])
  intro before a b fa fb first second
  exact PureDeterminism.block_unique
    (by simp [ZeroLoop.loopBody,zeroStoreStmt,ZeroLoop.increment,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem function_statements_unique {F : Type} (context : Context F) :
    ∀s∈functionStatements,CompareSource.Unique context s:=by
  intro stmt member
  simp only [functionStatements,List.mem_cons,List.mem_nil_iff,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact fun first second=>PureDeterminism.simple_unique (by simp [localDeclaration,ZeroSlice.localDeclaration,PureDeterminism.Simple,SourcePure.CallFree]) first second
  · exact loop_unique context
  · exact fun first second=>PureDeterminism.simple_unique (by simp [zeroReturn,ZeroSlice.zeroReturn,PureDeterminism.Simple,SourcePure.CallFree]) first second

theorem function_body_unique {F : Type} {context : Context F}
    {before a b : State F} {fa fb : Flow}
    (first : Body context functionStatements before functionStatements fa a)
    (second : Body context functionStatements before functionStatements fb b) : fa=fb ∧ a=b := by
  cases first with
  | finish run _=>
    cases second with
    | finish run' _=>exact CompareSource.list_unique (function_statements_unique context) run run'
    | jump run' target tail=>simp [functionStatements,localDeclaration,zeroReturn,ZeroSlice.localDeclaration,ZeroSlice.zeroReturn,ZeroLoop.loop,labelTail] at target
  | jump run target tail=>simp [functionStatements,localDeclaration,zeroReturn,ZeroSlice.localDeclaration,ZeroSlice.zeroReturn,ZeroLoop.loop,labelTail] at target

theorem returned_call_unique {F : Type} {context : Context F}
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before a b : State F} {args : List Value} {value : Value} {result : CallResult}
    (first : Call context "zero_words" args before (.value value) a)
    (second : Call context "zero_words" args before result b) : result=.value value ∧ b=a := by
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
      obtain ⟨flowEq,middleEq⟩:=function_body_unique bodyA bodyB
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
      cases (function_body_unique bodyA bodyB).1
  | internalVoid selectedA shapeA void paramsA bodyA finishA=>
    have functionA:=Option.some.inj (selected.symm.trans selectedA)
    subst_vars
    cases void

def zeroStatement : Stmt:=.expression (.call "zero_words" [.variable "work",.literal (.integer 10 "ULL")])

/-- A real known terminating zero_words expression forces every permitted
argument order and every competing execution to the same normal state. -/
theorem expression_from_known {F : Type} {context : Context F}
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    {before middle after : State F} {flow : Flow}
    (known : Exec context before zeroStatement .normal middle)
    (other : Exec context before zeroStatement flow after) : flow=.normal ∧ after=middle:=by
  have closed : ∀e∈[Expr.variable "work",Expr.literal (.integer 10 "ULL")],SourcePure.CallFree e:=by simp [SourcePure.CallFree]
  cases known with
  | expression evaluated=>
    cases evaluated with
    | call args called=>
      cases other with
      | expression evaluated'=>
        cases evaluated' with
        | call args' called'=>
          obtain ⟨rfl,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args args'
          exact ⟨rfl,(returned_call_unique selected called called').2⟩
        | load place loaded=>cases place
      | callTerminated args' called'=>
        obtain ⟨rfl,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args args'
        cases (returned_call_unique selected called called').1
    | load place loaded=>cases place

#print axioms returned_call_unique
#print axioms expression_from_known
end RH080Next.FFTPV.ZeroCallUnique
