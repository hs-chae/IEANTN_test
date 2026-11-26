/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTInputLoaderView
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.InputLoader
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings

/-- Values of future declarations are specifications only. PartialBindings
requires an actual slot solely for variables already declared by the source. -/
def plannedValues (input : Input) (j : Nat) : Var → Value
  | .inl p=> parameterValues input j p
  | .inr .e=>.integer (integer64 (input.profile.encoded j))
  | .inr .value | .inr .sign=>.integer (integer64 0)
  | .inr .scaled=>.integer (integer64 (InputCell.magnitudeValue (input.profile.encoded j)*100))
  | .inr .p=>.pointer (wordPointer input.object (12*j))

structure BodyView {F : Type} (state : State F) (input : Input) (functionOwner blockOwner count j cutoff : Nat)
    (ids : Var → Nat) (values : Var → Value) (memory : Nat → Nat) : Prop where
  array : WordArrayRep state input.object (12*input.profile.grid) memory
  bindings : PartialBindings state count functionOwner blockOwner ids values
  parameters : ∀p,values (.inl p)=parameterValues input j p
  separate : ∀v,Active count v → input.object≠ids v
  well : WellScoped state
  scope : state.scope=blockOwner
  active : j< input.profile.count
  fresh : cutoff≤ state.nextObject
  born : ∀t,Active count (.inr t) → cutoff≤ ids (.inr t)

theorem PartialBindings.congr_values {F : Type} {state : State F} {count fo bo : Nat}
    {ids : Var → Nat} {a b : Var → Value} (h : PartialBindings state count fo bo ids a)
    (same : ∀v,Active count v → a v=b v) : PartialBindings state count fo bo ids b:=by
  refine ⟨h.lookup,?_,h.distinct,h.bound⟩
  intro v hv;rw [←same v hv];exact h.slots v hv

theorem LoopView.enter_body {F : Type} {before : State F} {input : Input} {fo j : Nat} {ids : Parameter → Nat}
    (h : LoopView before input fo ids j) (hj : j< input.profile.count) :
    BodyView before.enterScope input fo before.nextScope 0 j before.nextObject (initialIds ids) (plannedValues input j)
      (currentData input.profile.encoded input.profile.grid j):=by
  refine ⟨h.array,h.enter.congr_values ?_,fun _=> rfl,?_,wellScoped_enter h.well,rfl,hj,le_refl _,?_⟩
  · intro v hv;cases v with
    | inl p=> rfl
    | inr t=> cases t <;> simp [Active,localIndex] at hv
  · intro v hv;cases v with
    | inl p=> exact h.separate p
    | inr t=> cases t <;> simp [Active,localIndex] at hv
  · intro t hv;cases t <;> simp [Active,localIndex] at hv

theorem BodyView.parameter_eval {F : Type} (context : Context F) {before : State F} {input : Input} {fo bo count j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat}
    (h : BodyView before input fo bo count j cutoff ids values memory) (p : Parameter) :
    Eval context before (.variable (parameterName p)) (parameterValues input j p) before:=by
  have evaluate:=Eval.variable (context:=context) (h.bindings.lookup (.inl p) (by trivial)) (h.bindings.read (.inl p) (by trivial))
  simpa only [varName,h.parameters p] using evaluate

theorem BodyView.after_call {F : Type} {before after : State F} {input : Input} {fo bo count j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat}
    (h : BodyView before input fo bo count j cutoff ids values memory) (frame : MultiplyCall.CallerFrame before after []) :
    BodyView after input fo bo count j cutoff ids values memory:=by
  have live:=h.well.objectIds _ _ h.array.2.1
  have array : WordArrayRep after input.object (12*input.profile.grid) memory:=
    ⟨frame.frame.mode.trans h.array.1,by rw [frame.frame.outside input.object live (by simp)];exact h.array.2.1,h.array.2.2⟩
  exact ⟨array,h.bindings.after_call h.well frame (by intros;simp),h.parameters,h.separate,frame.frame.well,
    frame.scope.trans h.scope,h.active,h.fresh.trans frame.frame.nextObject,h.born⟩

theorem BodyView.declare_next {F : Type} {before after : State F} {input : Input} {fo bo count j cutoff : Nat}
    {ids : Var → Nat} {values : Var → Value} {memory : Nat → Nat} {next : Temporary}
    (h : BodyView before input fo bo count j cutoff ids values memory) (index : localIndex next=count)
    (d : Declaration before after (temporaryName next) (varType (.inr next)) (values (.inr next)))
    (declared : before.declare (varType (.inr next)) (temporaryName next) (some (values (.inr next)))=some after) :
    BodyView after input fo bo (count+1) j cutoff (Function.update ids (.inr next) before.nextObject) values memory:=by
  have live:=h.well.objectIds _ _ h.array.2.1
  have born : ∀t,Active (count+1) (.inr t) → cutoff≤(Function.update ids (.inr next) before.nextObject) (.inr t):=by
    intro t ht
    by_cases same : t=next
    · subst t;simpa only [Function.update_self] using h.fresh
    · rw [Function.update_of_ne (show Sum.inr t≠Sum.inr next from by simpa using same)]
      exact h.born t (((active_step index (.inr t)).mp ht).resolve_left (by simpa using same))
  refine ⟨ApplicationBirthFrame.array_declare_old h.well h.array d,h.bindings.declare_next h.well h.scope index d,
    h.parameters,?_,wellScoped_declare h.well declared,d.scope.trans h.scope,h.active,by rw [d.nextObject];exact h.fresh.trans (Nat.le_succ _),born⟩
  intro v hv
  by_cases same : v=.inr next
  · subst v;rw [Function.update_self];omega
  · rw [Function.update_of_ne same]
    exact h.separate v (((active_step index v).mp hv).resolve_left same)

#print axioms LoopView.enter_body
#print axioms BodyView.declare_next
end RH080Next.FFTPV.InputLoader
