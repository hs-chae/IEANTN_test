/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitApplicationExpressionCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RootSource
open GoldbachDirect GoldbachDirect.Semantics

def Every {F : Type} (context : Context F) (before : State F) (stmt : Stmt) (flow : Flow) (after : State F) : Prop:=
  ∀other result,Exec context before stmt result other → result=flow ∧ other=after

def EveryList {F : Type} (context : Context F) (before : State F) (statements : List Stmt) (flow : Flow) (after : State F) : Prop:=
  ∀other result,ExecList context before statements result other → result=flow ∧ other=after

theorem every_of_unique {F : Type} {context : Context F} {before after : State F} {stmt : Stmt} {flow : Flow}
    (unique : CompareSource.Unique context stmt) (known : Exec context before stmt flow after) : Every context before stmt flow after:=by
  intro other result run
  obtain ⟨flowEq,stateEq⟩:=unique known run
  exact ⟨flowEq.symm,stateEq.symm⟩

theorem every_pure {F : Type} {context : Context F} {before after : State F} {stmt : Stmt} {flow : Flow}
    (simple : PureDeterminism.Simple stmt) (known : Exec context before stmt flow after) : Every context before stmt flow after:=by
  intro other result run
  obtain ⟨flowEq,stateEq⟩:=PureDeterminism.simple_unique simple known run
  exact ⟨flowEq.symm,stateEq.symm⟩

/-- A known returning internal application call determines the whole source
expression statement, including the separately permitted terminated-call rule. -/
theorem every_expression_call {F : Type} {context : Context F} {before after : State F}
    {cname : String} {expressions : List Expr} {values : List Value} {value : Value}
    (closed : ∀e∈expressions,SourcePure.CallFree e)
    (args : Args context before expressions values before)
    (callee : ∀state output,Call context cname values before output state → output=.value value ∧ state=after) :
    Every context before (.expression (.call cname expressions)) .normal after := by
  intro other result run
  cases run with
  | expression evaluated=>
    cases evaluated with
    | call actualArgs actualCall=>
      obtain ⟨_,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args actualArgs
      obtain ⟨_,stateEq⟩:=callee _ _ actualCall
      exact ⟨rfl,stateEq⟩
    | load place read=>cases place
  | callTerminated actualArgs actualCall=>
    obtain ⟨_,rfl,rfl⟩:=ApplicationPureCall.args_unique closed args actualArgs
    cases (callee _ _ actualCall).1

theorem every_nil {F : Type} {context : Context F} (before : State F) : EveryList context before [] .normal before:=by
  intro other result run;cases run;exact ⟨rfl,rfl⟩

theorem every_cons {F : Type} {context : Context F} {before middle after : State F} {stmt : Stmt} {tail : List Stmt} {flow : Flow}
    (head : Every context before stmt .normal middle) (rest : EveryList context middle tail flow after) :
    EveryList context before (stmt::tail) flow after := by
  intro other result run
  cases run with
  | cons first last=>
    obtain ⟨_,rfl⟩:=head _ _ first
    exact rest _ _ last
  | abrupt first bad=>exact False.elim (bad (head _ _ first).1)

theorem every_abrupt {F : Type} {context : Context F} {before after : State F} {stmt : Stmt} {tail : List Stmt} {flow : Flow}
    (known : Every context before stmt flow after) (abrupt : flow≠.normal) :
    EveryList context before (stmt::tail) flow after := by
  intro other result run
  cases run with
  | cons first last=>exact False.elim (abrupt (known _ _ first).1.symm)
  | abrupt first bad=>exact known _ _ first

private theorem split_execution {F : Type} {context : Context F} {before after : State F} {flow : Flow}
    (xs ys : List Stmt) (run : ExecList context before (xs++ys) flow after) :
    (∃middle,ExecList context before xs .normal middle ∧ ExecList context middle ys flow after) ∨
      (ExecList context before xs flow after ∧ flow≠.normal) := by
  induction xs generalizing before with
  | nil=>exact Or.inl ⟨before,.nil,run⟩
  | cons stmt xs ih=>
    cases run with
    | abrupt first bad=>exact Or.inr ⟨.abrupt first bad,bad⟩
    | cons first last=>
      rcases ih last with ⟨middle,prefixRun,suffixRun⟩|⟨prefixRun,bad⟩
      · exact Or.inl ⟨middle,.cons first prefixRun,suffixRun⟩
      · exact Or.inr ⟨.cons first prefixRun,bad⟩

theorem every_append {F : Type} {context : Context F} {before middle after : State F} {xs ys : List Stmt} {flow : Flow}
    (first : EveryList context before xs .normal middle) (last : EveryList context middle ys flow after) :
    EveryList context before (xs++ys) flow after := by
  intro other result run
  rcases split_execution xs ys run with ⟨cut,prefixRun,suffixRun⟩|⟨prefixRun,bad⟩
  · obtain ⟨_,rfl⟩:=first _ _ prefixRun
    exact last _ _ suffixRun
  · exact False.elim (bad (first _ _ prefixRun).1)

theorem every_block {F : Type} {context : Context F} {before middle : State F} {body : List Stmt} {flow : Flow}
    (known : EveryList context before.enterScope body flow middle) :
    Every context before (.block body) flow {middle.leaveScope before.nextScope before.environment with scope:=before.scope} := by
  intro other result run
  cases run with
  | block entered bodyRun finished=>
    subst_vars
    obtain ⟨rfl,rfl⟩:=known _ _ bodyRun
    exact ⟨rfl,rfl⟩

theorem every_while_false {F : Type} {context : Context F} {before : State F} {condition : Expr} {body : Stmt} {value : Value}
    (closed : SourcePure.CallFree condition) (eval : Eval context before condition value before) (test : value.truth=some false) :
    Every context before (.whileLoop condition body) .normal before := by
  intro other result run
  cases run with
  | whileFalse observed observedTest=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    exact ⟨rfl,rfl⟩
  | whileNext observed observedTest bodyRun rest=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    cases test.symm.trans observedTest
  | whileContinue observed observedTest bodyRun rest=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    cases test.symm.trans observedTest
  | whileBreak observed observedTest bodyRun=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    cases test.symm.trans observedTest
  | whileExit observed observedTest bodyRun abrupt=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    cases test.symm.trans observedTest

theorem every_while_next {F : Type} {context : Context F} {before middle after : State F}
    {condition : Expr} {body : Stmt} {value : Value} {flow : Flow}
    (closed : SourcePure.CallFree condition) (eval : Eval context before condition value before) (test : value.truth=some true)
    (step : Every context before body .normal middle) (rest : Every context middle (.whileLoop condition body) flow after) :
    Every context before (.whileLoop condition body) flow after := by
  intro other result run
  cases run with
  | whileFalse observed observedTest=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    cases test.symm.trans observedTest
  | whileNext observed observedTest bodyRun last=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    obtain ⟨_,rfl⟩:=step _ _ bodyRun
    exact rest _ _ last
  | whileContinue observed observedTest bodyRun last=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    cases (step _ _ bodyRun).1
  | whileBreak observed observedTest bodyRun=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    cases (step _ _ bodyRun).1
  | whileExit observed observedTest bodyRun abrupt=>
    obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed eval observed
    exact False.elim (abrupt.1 (step _ _ bodyRun).1)

def EveryCall {F : Type} (context : Context F) (before : State F) (name : String) (arguments : List Value)
    (result : CallResult) (after : State F) : Prop:=
  ∀other output,Call context name arguments before output other → output=result ∧ other=after

/-- Determinism at the actual proved function entry suffices; no invalid global
alias-insensitive determinism assertion is made about status/callee expressions. -/
theorem every_call_from_body {F : Type} {context : Context F} {before entered finished after : State F}
    {name : String} {function : Function} {arguments : List Value} {statements : List Stmt} {raw value : Value}
    (selected : findFunction context.program name=some function) (shape : function.body=.block statements)
    (notVoid : function.result≠.void)
    (parameters : bindParameters {before.enterScope with environment:=[]} function.parameters arguments=some entered)
    (body : EveryList context entered statements (.returned raw) finished)
    (labels : ∀label,labelTail label statements=none)
    (converted : Value.convert function.result raw=some value)
    (completed : after={finished.leaveScope entered.scope before.environment with scope:=before.scope}) :
    EveryCall context before name arguments (.value value) after := by
  have bodyUnique : ∀{other : State F} {flow : Flow},Body context statements entered statements flow other →
      flow=.returned raw ∧ other=finished:=by
    intro other flow execution
    cases execution with
    | finish run noJump=>exact body _ _ run
    | jump prefixRun target tailRun=>rw [labels] at target;cases target
  intro other output execution
  cases execution with
  | external absent named foreign=>rw [selected] at absent;cases absent
  | internal chosen actualShape actualParameters actualBody conversion completion=>
    have functionEq:=Option.some.inj (selected.symm.trans chosen)
    subst_vars
    have statementsEq:=Stmt.block.inj (shape.symm.trans actualShape)
    subst_vars
    have enteredEq:=Option.some.inj (parameters.symm.trans actualParameters)
    subst_vars
    obtain ⟨flowEq,middleEq⟩:=bodyUnique actualBody
    have rawEq:=Flow.returned.inj flowEq
    cases rawEq
    cases middleEq
    have valueEq:=Option.some.inj (converted.symm.trans conversion)
    cases valueEq
    exact ⟨rfl,rfl⟩
  | internalVoid chosen actualShape void actualParameters actualBody completion=>
    have functionEq:=Option.some.inj (selected.symm.trans chosen)
    subst_vars
    exact False.elim (notVoid void)
  | internalTerminated chosen actualShape actualParameters actualBody=>
    have functionEq:=Option.some.inj (selected.symm.trans chosen)
    subst_vars
    have statementsEq:=Stmt.block.inj (shape.symm.trans actualShape)
    subst_vars
    have enteredEq:=Option.some.inj (parameters.symm.trans actualParameters)
    subst_vars
    cases (bodyUnique actualBody).1

#print axioms every_expression_call
#print axioms every_append
#print axioms every_block
#print axioms every_while_next
#print axioms every_call_from_body
end RH080Next.FFTPV.RootSource
