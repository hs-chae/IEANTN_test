/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderBirths
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open RootSource

private theorem store_exists {F : Type} {state : State F} {id scope : Nat} {ctype : CType} {oldValue : Value}
    (slot : Slot state id scope ctype oldValue) (value : Value) (storable : Storable ctype value) :
    ∃after,state.store (scalarPointer id ctype) value=some after:=by
  obtain ⟨oldType,present⟩:=slot
  have same : oldValue.byteSize=value.byteSize:=Option.some.inj (oldType.typeWidth.symm.trans storable.typeWidth)
  rw [same] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,storable.typeWidth,storable.converted]

theorem BodyView.assign {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo count j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat} (h : BodyView before input fo bo count j cutoff ids values memory)
    (target : Temporary) (active : Active count (.inr target)) (value : Value) (expression : Expr)
    (storable : Storable (varType (.inr target)) value)
    (evaluated : Eval context before expression value before) (pure : SourcePure.CallFree expression) :
    ∃after,Exec context before (.assign (.variable (temporaryName target)) expression) .normal after ∧
      Every context before (.assign (.variable (temporaryName target)) expression) .normal after ∧
      BodyView after input fo bo count j cutoff ids (Function.update values (.inr target) value) memory ∧
      ApplicationBirthFrame.Frame cutoff before after []:=by
  obtain ⟨after,stored⟩:=store_exists (h.bindings.slots (.inr target) active) value storable
  have run : Exec context before (.assign (.variable (temporaryName target)) expression) .normal after:=
    .assign evaluated (.variable (h.bindings.lookup (.inr target) active)) stored
  have fields:=SourceLocals.store_frame stored
  have live : input.object≠(scalarPointer (ids (.inr target)) (varType (.inr target))).object:=h.separate (.inr target) active
  have array : WordArrayRep after input.object (12*input.profile.grid) memory:=
    ⟨fields.2.1.trans h.array.1,by rw [fields.2.2.2.2.2 _ live];exact h.array.2.1,h.array.2.2⟩
  have frame:=ApplicationBirthFrame.store_frame cutoff [] h.well h.fresh
    (Or.inr (by simpa only [scalarPointer] using h.born target active)) stored
  have post : BodyView after input fo bo count j cutoff ids (Function.update values (.inr target) value) memory:=
    ⟨array,h.bindings.store (.inr target) active value storable stored,
      (by intro p;rw [Function.update_of_ne (show Sum.inl p≠Sum.inr target from by intro same;cases same)];exact h.parameters p),
      h.separate,frame.well,fields.2.2.1.trans h.scope,h.active,frame.fresh,h.born⟩
  exact ⟨after,run,every_pure ⟨by trivial,pure⟩ run,post,frame⟩

theorem BodyView.variable {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo count j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat} (h : BodyView before input fo bo count j cutoff ids values memory)
    (t : Temporary) (active : Active count (.inr t)) : Eval context before (.variable (temporaryName t)) (values (.inr t)) before:=
  .variable (h.bindings.lookup (.inr t) active) (h.bindings.read (.inr t) active)

#print axioms BodyView.assign
end RH080Next.FFTPV.InputLoader
