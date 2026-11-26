/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplyFrame
import ExplicitApplicationPureCall
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.StatusCall
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots

/-- Storing an unchanged value in a real single-value automatic object is
idempotent under the actual typed store/overlap semantics. -/
theorem slot_store_same {F : Type} {state : State F} {id owner : Nat} {type : CType} {value : Value}
    (slot : Slot state id owner type value) : state.store (scalarPointer id type) value=some state := by
  simp [State.store,scalarPointer,slot.object,State.accessible,scalarObject,
    slot.storable.typeWidth,slot.storable.converted]
  congr 1
  funext j
  by_cases equal : j=id
  · subst j
    rw [if_pos rfl,slot.object]
    congr 1
    congr 1
    funext offset
    by_cases zero : offset=0 <;> simp [scalarObject,zero]
  · simp [equal]

def statement (cname : String) (arguments : List Expr) : Stmt:=
  .assign (.variable "status") (.paren (.binary .add (.variable "status") (.call cname arguments)))

theorem assignment_execution {F : Type} {context : Context F} {before after : State F}
    {id owner : Nat} {cname : String} {expressions : List Expr} {values : List Value}
    (lookup : before.environment.lookup "status"=some (scalarPointer id .u64))
    (afterLookup : after.environment.lookup "status"=some (scalarPointer id .u64))
    (slot : Slot before id owner .u64 (.integer (integer64 0)))
    (afterSlot : Slot after id owner .u64 (.integer (integer64 0)))
    (args : Args context before expressions values before)
    (called : Call context cname values before (.value (.integer (integer64 0))) after) :
    Exec context before (statement cname expressions) .normal after:=by
  exact .assign (.paren (.binaryLR (.variable lookup slot.read) (.call args called)
    (by rfl))) (.variable afterLookup) (slot_store_same afterSlot)

/-- Unique returned call value/state for the actual source argument positions;
every permitted argument permutation is handled by the independent pure-Args theorem. -/
theorem call_eval_unique {F : Type} {context : Context F} {before after other : State F}
    {cname : String} {expressions : List Expr} {values : List Value} {value result : Value}
    (closed : ∀e∈expressions,SourcePure.CallFree e)
    (args : Args context before expressions values before)
    (callee : ∀state output,Call context cname values before output state → output=.value value ∧ state=after)
    (run : Eval context before (.call cname expressions) result other) : result=value ∧ other=after:=by
  cases run with
  | call actualArgs actualCall=>
    obtain ⟨_,entryEq,valuesEq⟩:=ApplicationPureCall.args_unique closed args actualArgs
    cases entryEq
    cases valuesEq
    obtain ⟨outputEq,stateEq⟩:=callee _ _ actualCall
    exact ⟨CallResult.value.inj outputEq,stateEq⟩
  | load place read=>cases place

/-- The source's status += zero-returning-call expression is deterministic
under BOTH operand evaluation orders, using the callee's proved status-slot frame. -/
theorem status_eval_unique {F : Type} {context : Context F} {before after other : State F}
    {id owner : Nat} {cname : String} {expressions : List Expr} {values : List Value} {result : Value}
    (lookup : before.environment.lookup "status"=some (scalarPointer id .u64))
    (afterLookup : after.environment.lookup "status"=some (scalarPointer id .u64))
    (slot : Slot before id owner .u64 (.integer (integer64 0)))
    (afterSlot : Slot after id owner .u64 (.integer (integer64 0)))
    (closed : ∀e∈expressions,SourcePure.CallFree e)
    (args : Args context before expressions values before)
    (callee : ∀state output,Call context cname values before output state →
      output=.value (.integer (integer64 0)) ∧ state=after)
    (run : Eval context before (.paren (.binary .add (.variable "status") (.call cname expressions))) result other) :
    result=.integer (integer64 0) ∧ other=after:=by
  cases run with
  | paren run=>
    cases run with
    | binaryLR left right computed=>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial : SourcePure.CallFree (.variable "status"))
        (.variable lookup slot.read) left
      obtain ⟨rfl,rfl⟩:=call_eval_unique closed args callee right
      exact ⟨Option.some.inj computed.symm,rfl⟩
    | binaryRL right left computed=>
      obtain ⟨rfl,rfl⟩:=call_eval_unique closed args callee right
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial : SourcePure.CallFree (.variable "status"))
        (.variable afterLookup afterSlot.read) left
      exact ⟨Option.some.inj computed.symm,rfl⟩
    | load place read=>cases place
  | load place read=>cases place with
    | paren place=>cases place

theorem assignment_every_execution {F : Type} {context : Context F} {before after other : State F}
    {id owner : Nat} {cname : String} {expressions : List Expr} {values : List Value} {flow : Flow}
    (lookup : before.environment.lookup "status"=some (scalarPointer id .u64))
    (afterLookup : after.environment.lookup "status"=some (scalarPointer id .u64))
    (slot : Slot before id owner .u64 (.integer (integer64 0)))
    (afterSlot : Slot after id owner .u64 (.integer (integer64 0)))
    (closed : ∀e∈expressions,SourcePure.CallFree e)
    (args : Args context before expressions values before)
    (callee : ∀state output,Call context cname values before output state →
      output=.value (.integer (integer64 0)) ∧ state=after)
    (run : Exec context before (statement cname expressions) flow other) : flow=.normal ∧ other=after:=by
  cases run with
  | assign right left stored=>
    obtain ⟨valueEq,stateEq⟩:=status_eval_unique lookup afterLookup slot afterSlot closed args callee right
    have place : Place context after (.variable "status") (scalarPointer id .u64) after:=.variable afterLookup
    have left' : Place context after (.variable "status") _ _:=stateEq ▸ left
    obtain ⟨pointerEq,assignedEq⟩:=PureDeterminism.place_unique (by trivial) place left'
    rw [←pointerEq,←assignedEq,valueEq] at stored
    exact ⟨rfl,Option.some.inj (stored.symm.trans (slot_store_same afterSlot))⟩

#print axioms slot_store_same
#print axioms assignment_execution
#print axioms status_eval_unique
#print axioms assignment_every_execution
end RH080Next.FFTPV.StatusCall
