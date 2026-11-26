/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadBase
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

structure LoopView {F : Type} (state : State F) (input : InputLoader.Input) (workObject fo j : Nat)
    (paramIds : Parameter → Nat) (auxIds : Aux → Nat) (dataMemory workData : Nat → Nat) : Prop where
  parameters : Locals state parameterName parameterType paramIds fo (parameterValues input j)
  aux : Locals state auxName auxType auxIds fo (auxValues workObject)
  array : WordArrayRep state input.object (12*input.profile.grid) dataMemory
  work : WordArrayRep state workObject 512 workData
  different : input.object≠workObject
  dataSeparate : ∀p,input.object≠paramIds p
  workSeparate : ∀p,workObject≠paramIds p
  auxSeparate : ∀v,workObject≠auxIds v
  cross : ∀p v,paramIds p≠auxIds v
  active : j≤ input.profile.count
  quadDigits : ∀d<6,workData (208+d)< base
  quadValue : FFT.Limbs.magnitude base 6 (fun d=> workData (208+d))=partialQuad input.profile j
  well : WellScoped state

theorem LoopView.enter_body {F : Type} {before : State F} {input : InputLoader.Input} {workObject fo j : Nat}
    {paramIds : Parameter → Nat} {auxIds : Aux → Nat} {dataMemory workData : Nat → Nat}
    (h : LoopView before input workObject fo j paramIds auxIds dataMemory workData) (hj : j< input.profile.count) :
    View before.enterScope input workObject fo before.nextScope 0 j before.nextObject (initialIds paramIds) auxIds (plannedValues input j) dataMemory workData:=by
  have bindings : PartialBindings before.enterScope 0 fo before.nextScope (initialIds paramIds) (plannedValues input j):=by
    refine ⟨?_,?_,?_,?_⟩
    · intro v hv
      cases v with
      | inl p=> cases p with
        | data=> exact h.parameters.lookup .data
        | n=> exact h.parameters.lookup .n
        | j=> exact h.parameters.lookup .j
      | inr t=> cases t <;> simp [Active,localIndex] at hv
    · intro v hv
      cases v with
      | inl p=> cases p with
        | data=> exact ⟨(h.parameters.slots .data).storable,(h.parameters.slots .data).object⟩
        | n=> exact ⟨(h.parameters.slots .n).storable,(h.parameters.slots .n).object⟩
        | j=> exact ⟨(h.parameters.slots .j).storable,(h.parameters.slots .j).object⟩
      | inr t=> cases t <;> simp [Active,localIndex] at hv
    · intro a b ha hb same
      cases a with
      | inl a=> cases b with
        | inl b=> exact congrArg Sum.inl (h.parameters.distinct same)
        | inr b=> cases b <;> simp [Active,localIndex] at hb
      | inr a=> cases a <;> simp [Active,localIndex] at ha
    · intro v hv
      cases v with
      | inl p=> have b:=h.parameters.bound;change fo< before.nextScope+1;omega
      | inr t=> cases t <;> simp [Active,localIndex] at hv
  have body : BodyView before.enterScope input fo before.nextScope 0 j before.nextObject (initialIds paramIds) (plannedValues input j) dataMemory:=by
    refine ⟨h.array,bindings,fun _=> rfl,?_,wellScoped_enter h.well,rfl,hj,le_refl _,?_⟩
    · intro v hv;cases v with
      | inl p=> exact h.dataSeparate p
      | inr t=> cases t <;> simp [Active,localIndex] at hv
    · intro t hv;cases t <;> simp [Active,localIndex] at hv
  refine ⟨body,h.aux.enter,h.work,h.different,?_,h.auxSeparate,?_,h.cross,h.quadDigits,?_⟩
  · intro v hv;cases v with
    | inl p=> exact h.workSeparate p
    | inr t=> cases t <;> simp [Active,localIndex] at hv
  · intro v;exact h.well.objectIds _ _ (h.aux.slots v).object
  · simpa using h.quadValue

#print axioms LoopView.enter_body
end RH080Next.FFTPV.QuadSource
