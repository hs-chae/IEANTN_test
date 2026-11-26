/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixRound
import ExplicitApplicationPureCall
import FFTCanonicalDeterminism
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

def UniqueAt {F : Type} (context : Context F) (before : State F) (stmt : Stmt) : Prop :=
  ∀{a b : State F} {fa fb : Flow}, Exec context before stmt fa a → Exec context before stmt fb b → fa=fb ∧ a=b

private theorem increment_args {F : Type} (context : Context F) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    Args context before [v "out",lit 5] [.pointer (wordPointer outObj outStart),.integer (integer64 5)] before := by
  apply Args.ordered (order := [(0,v "out"),(1,lit 5)]) (evaluated :=
    [(0,.pointer (wordPointer outObj outStart)),(1,.integer (integer64 5))]) (by rfl)
  · exact .cons (.variable (h.locals.lookup (.inl MVar.out)) (h.locals.read (.inl MVar.out)))
      (.cons (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl)) .nil)
  · exact .cons (by rfl) (.cons (by rfl) .nil)

private theorem increment_call_value {F : Type} {context : Context F}
    (selected : findFunction context.program "increment_words"=some increment_words_ast)
    {before called after : State F} {outObj outSize outStart workObj workSize workStart sign lost overflow carry : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow)
    (known : Call context "increment_words" [.pointer (wordPointer outObj outStart),.integer (integer64 5)] before
      (.value (.integer (integer64 carry))) called) {value : Value}
    (run : Eval context before incrementCall value after) : value=.integer (integer64 carry) ∧ after=called := by
  cases run with
  | call args call =>
    obtain ⟨_,stateEq,same⟩:=ApplicationPureCall.args_unique
      (by intro e member;simp [v,lit,SourcePure.CallFree] at member ⊢;rcases member with rfl|rfl <;> trivial)
      (increment_args context h) args
    cases stateEq
    cases same
    obtain ⟨valueEq,stateEq⟩:=IncrementSource.returned_call_unique selected known call
    cases valueEq
    exact ⟨rfl,stateEq⟩
  | load place loaded => cases place

/-- The source binary expression is deterministic even across its two legal
operand orders. The real helper frame preserves the overflow slot when the
call is evaluated first. That disjointness is essential, not assumed globally. -/
theorem increment_overflow_unique_at {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    UniqueAt context before incrementOverflow := by
  obtain ⟨called,known,outAfter,frame⟩:=IncrementSource.increment_words_call_framed context selected before
    outObj outSize outStart 5 outData h.well h.output (by have hb:=h.outBound;omega) (by omega) h.digits
  let carry := (FFT.Limbs.incrementDigits 1000000000 (fun k => outData (outStart+k)) 5).2
  have carryBound : carry≤1:=
    (FFT.Limbs.incrementDigits_bounds 1000000000 5 (by norm_num) (fun k => outData (outStart+k)) h.digits).1
  have leftBefore : Eval context before (v "overflow") (.integer (integer64 overflow)) before :=
    .variable (h.locals.lookup (.inr ())) (h.locals.read (.inr ()))
  have slot:=h.locals.slots (.inr ())
  have slotAfter : Slot called (ids (.inr ())) (owners (.inr ())) .u64 (.integer (integer64 overflow)) :=
    ⟨slot.storable,(frame.objects _ (h.well.objectIds _ _ slot.object) (h.separate (.inr ())).1.symm).trans slot.object⟩
  have nameAfter : called.environment.lookup "overflow"=some (scalarPointer (ids (.inr ())) .u64) := by
    rw [frame.environment];exact h.locals.lookup (.inr ())
  have leftAfter : Eval context called (v "overflow") (.integer (integer64 overflow)) called :=
    .variable nameAfter slotAfter.read
  have computed : binary called .add (.integer (integer64 overflow)) (.integer (integer64 carry))=
      some (.integer (integer64 (overflow+carry))) := by
    simp only [binary,binary64_add overflow carry (by have ho:=h.overflowBound;omega)
      (by omega) (by have ho:=h.overflowBound;omega),Option.map_some]
  have expression : ∀{after : State F} {value : Value},
      Eval context before (.paren (.binary .add (v "overflow") incrementCall)) value after →
      value=.integer (integer64 (overflow+carry)) ∧ after=called := by
    intro after value run
    cases run with
    | paren inner =>
      cases inner with
      | binaryLR left right result =>
        obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) leftBefore left
        obtain ⟨rfl,rfl⟩:=increment_call_value selected h known right
        exact ⟨Option.some.inj (result.symm.trans computed),rfl⟩
      | binaryRL right left result =>
        obtain ⟨rfl,rfl⟩:=increment_call_value selected h known right
        obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique (by trivial) leftAfter left
        exact ⟨Option.some.inj (result.symm.trans computed),rfl⟩
      | load place loaded => cases place
    | load place loaded => cases place with | paren place => cases place
  intro a b fa fb first second
  cases first with | assign ev pl stored =>
    cases second with | assign ev' pl' stored' =>
      obtain ⟨rfl,rfl⟩:=expression ev
      obtain ⟨rfl,rfl⟩:=expression ev'
      obtain ⟨rfl,rfl⟩:=PureDeterminism.place_unique (by trivial) pl pl'
      exact ⟨rfl,Option.some.inj (stored.symm.trans stored')⟩

private theorem singleton_unique_at {F : Type} {context : Context F} {before a b : State F}
    {stmt : Stmt} {fa fb : Flow} (unique : UniqueAt context before stmt)
    (first : ExecList context before [stmt] fa a) (second : ExecList context before [stmt] fb b) : fa=fb ∧ a=b := by
  cases first with
  | cons run rest =>
    cases rest
    cases second with
    | cons run' rest' => cases rest';exact unique run run'
    | abrupt run' ne => exact False.elim (ne (unique run run').1.symm)
  | abrupt run ne =>
    cases second with
    | cons run' rest' => exact False.elim (ne (unique run run').1)
    | abrupt run' ne' => exact unique run run'

private theorem singleton_block_unique_at {F : Type} {context : Context F} {before : State F} {stmt : Stmt}
    (unique : UniqueAt context before.enterScope stmt) : UniqueAt context before (.block [stmt]) := by
  intro a b fa fb first second
  cases first with | block start run closed =>
    cases second with | block start' run' closed' =>
      subst_vars
      obtain ⟨rfl,rfl⟩:=singleton_unique_at unique run run'
      exact ⟨rfl,rfl⟩

private theorem ite_unique_at {F : Type} {context : Context F} {before : State F} {condition : Expr} {yes : Stmt}
    (closed : SourcePure.CallFree condition) (unique : UniqueAt context before yes) :
    UniqueAt context before (.ite condition yes none) := by
  intro a b fa fb first second
  cases first with
  | ifTrue ev truth body =>
    have state:=SourcePure.eval_state ev closed
    cases state
    cases second with
    | ifTrue ev' truth' body' =>
      obtain ⟨rfl,rfl⟩:=PureDeterminism.eval_unique closed ev ev'
      exact unique body body'
    | ifFalse ev' truth' =>
      have eq:=(PureDeterminism.eval_unique closed ev ev').1
      cases eq
      simp_all
  | ifFalse ev truth =>
    have state:=SourcePure.eval_state ev closed
    cases state
    cases second with
    | ifTrue ev' truth' body' =>
      have eq:=(PureDeterminism.eval_unique closed ev ev').1
      cases eq
      simp_all
    | ifFalse ev' truth' => exact ⟨rfl,(PureDeterminism.eval_unique closed ev ev').2⟩

/-- Universal uniqueness of the actual nested rounding branch under the true
caller/data separation precondition. It covers both binary and argument orders. -/
theorem rounding_unique_at {F : Type} (context : Context F)
    (selected : findFunction context.program "increment_words"=some increment_words_ast) {before : State F}
    {outObj outSize outStart workObj workSize workStart sign lost overflow : Nat}
    {ids owners : TVar → Nat} {outData scratch : Nat → Nat}
    (h : RoundView before outObj outSize outStart workObj workSize workStart ids owners outData scratch sign lost overflow) :
    UniqueAt context before roundingBranch := by
  apply ite_unique_at (by simp [roundCondition,v,lit,SourcePure.CallFree])
  apply singleton_block_unique_at
  apply ite_unique_at (by simp [lostPositive,v,lit,SourcePure.CallFree])
  apply singleton_block_unique_at
  exact increment_overflow_unique_at context selected h.enter.enter

#print axioms increment_overflow_unique_at
#print axioms rounding_unique_at
end RH080Next.FFTPV.MultiplySuffix
