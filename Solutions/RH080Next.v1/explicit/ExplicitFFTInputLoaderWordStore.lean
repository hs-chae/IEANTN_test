/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderPreparation
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

theorem frame_widen {F : Type} {before after : State F} {cutoff : Nat} {small large : List Nat}
    (h : ApplicationBirthFrame.Frame cutoff before after small) (included : ∀id,id∈small → id∈large) :
    ApplicationBirthFrame.Frame cutoff before after large:=
  ⟨h.well,h.fresh,h.nextObject,h.nextScope,h.mode,h.foreign,
    fun id old absent=> h.outside id old (fun member=> absent (included id member))⟩

def wordAssignment (offset : Nat) (expression : Expr) : Stmt:=
  .assign (.index (.variable "p") (.literal (.integer offset "ULL"))) expression

theorem BodyView.word_store {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat}
    (h : BodyView before input fo bo 5 j cutoff ids values memory) (offset result : Nat) (offsetBound : offset<6)
    (expression : Expr) (evaluated : Eval context before expression (.integer (integer64 result)) before)
    (pure : SourcePure.CallFree expression) (result64 : result<2^64)
    (pointerValue : values (.inr .p)=.pointer (wordPointer input.object (12*j))) :
    ∃after,Exec context before (wordAssignment offset expression) .normal after ∧ Every context before (wordAssignment offset expression) .normal after ∧
      BodyView after input fo bo 5 j cutoff ids values (Function.update memory (12*j+offset) result) ∧
      ApplicationBirthFrame.Frame cutoff before after [input.object]:=by
  have shape:=input.profile.shape
  have bound : 12*j+offset<12*input.profile.grid:=by have active:=h.active;omega
  have offset64 : offset<2^64:=by omega
  obtain ⟨after,stored,array⟩:=word_store_with_rep h.array bound result64
  have pointerRead : Eval context before (.variable "p") (.pointer (wordPointer input.object (12*j))) before:=by
    simpa only [temporaryName,pointerValue] using h.variable context .p (by norm_num [Active,localIndex])
  have place : Place context before (.index (.variable "p") (.literal (.integer offset "ULL"))) (wordPointer input.object (12*j+offset)) before:=
    .index pointerRead (.literal _ _ _ (by have ho : offset<18446744073709551616:=offset64;simp [Literal.value,integer64,ho])) (slice_pointer_add h.array bound)
  have run : Exec context before (wordAssignment offset expression) .normal after:=.assign evaluated place stored
  have frame:=ApplicationBirthFrame.store_frame cutoff [input.object] h.well h.fresh (Or.inl (by simp [wordPointer])) stored
  have fields:=SourceLocals.store_frame stored
  have bindings:=h.bindings.store_other (fun v hv=> by simpa only [wordPointer] using (h.separate v hv).symm) stored
  exact ⟨after,run,every_pure ⟨by trivial,pure⟩ run,
    ⟨array,bindings,h.parameters,h.separate,frame.well,fields.2.2.1.trans h.scope,h.active,frame.fresh,h.born⟩,frame⟩

#print axioms BodyView.word_store
end RH080Next.FFTPV.InputLoader
