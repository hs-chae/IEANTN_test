/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitApplicationBirthFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductInner
open GoldbachDirect SourceLocals SourceScalarSlots
/-- Actual multiplication bindings have different lifetime owners: parameters
and i belong to the function, whereas j/carry belong to the outer row block. -/
structure Bindings {F I : Type} (state : State F) (names : I→String) (types : I→CType)
    (ids owners : I→Nat) (values : I→Value) : Prop where
  lookup : ∀v,state.environment.lookup (names v)=some (scalarPointer (ids v) (types v))
  slots : ∀v,Slot state (ids v) (owners v) (types v) (values v)
  distinct : Function.Injective ids
  bound : ∀v,owners v<state.nextScope

theorem Bindings.read {F I : Type} {state : State F} {names : I→String} {types : I→CType}
    {ids owners : I→Nat} {values : I→Value} (h : Bindings state names types ids owners values) (v : I) :
    state.load (scalarPointer (ids v) (types v))=some (values v):=(h.slots v).read

theorem Bindings.enter {F I : Type} {state : State F} {names : I→String} {types : I→CType}
    {ids owners : I→Nat} {values : I→Value} (h : Bindings state names types ids owners values) :
    Bindings state.enterScope names types ids owners values:=
  ⟨h.lookup,(fun v=>⟨(h.slots v).storable,(h.slots v).object⟩),h.distinct,fun v=>by have hb:=h.bound v;change owners v<state.nextScope+1;omega⟩

theorem Bindings.declare {F I : Type} {before after : State F} {names : I→String} {types : I→CType}
    {ids owners : I→Nat} {values : I→Value} {cname : String} {ctype : CType} {value : Value}
    (h : Bindings before names types ids owners values) (well : WellScoped before)
    (different : ∀v,names v≠cname) (d : Declaration before after cname ctype value) :
    Bindings after names types ids owners values := by
  refine ⟨?_,fun v=>ApplicationBirthFrame.slot_declare_old well (h.slots v) d,h.distinct,?_⟩
  · intro v;rw [d.environment]
    simpa [List.lookup,show (names v==cname)=false from by simp [different v]] using h.lookup v
  · intro v;rw [d.nextScope];exact h.bound v

theorem Bindings.store {F I : Type} [DecidableEq I] {before after : State F}
    {names : I→String} {types : I→CType} {ids owners : I→Nat} {values : I→Value}
    (h : Bindings before names types ids owners values) (v : I) (value : Value)
    (storable : Storable (types v) value)
    (written : before.store (scalarPointer (ids v) (types v)) value=some after) :
    Bindings after names types ids owners (Function.update values v value) := by
  obtain ⟨env,_,_,ns,_,outside⟩:=SourceLocals.store_frame written
  refine ⟨by rw [env];exact h.lookup,?_,h.distinct,fun v=>by rw [ns];exact h.bound v⟩
  intro u
  by_cases same : u=v
  · subst u;simpa using (h.slots v).store storable written
  · rw [Function.update_of_ne same]
    exact ApplicationBirthFrame.slot_store_other (h.slots u) (by intro eq;exact same (h.distinct eq)) written

theorem Bindings.store_other {F I : Type} {before after : State F}
    {names : I→String} {types : I→CType} {ids owners : I→Nat} {values : I→Value}
    {pointer : Pointer} {value : Value}
    (h : Bindings before names types ids owners values) (different : ∀v,ids v≠pointer.object)
    (written : before.store pointer value=some after) : Bindings after names types ids owners values := by
  obtain ⟨env,_,_,ns,_,_⟩:=SourceLocals.store_frame written
  exact ⟨by rw [env];exact h.lookup,
    fun v=>ApplicationBirthFrame.slot_store_other (h.slots v) (different v) written,h.distinct,
    fun v=>by rw [ns];exact h.bound v⟩

theorem Bindings.leave {F I : Type} {state : State F} {names : I→String} {types : I→CType}
    {ids owners : I→Nat} {values : I→Value} {scope restore : Nat}
    (h : Bindings state names types ids owners values) (different : ∀v,scope≠owners v)
    (environment : List (String×Pointer))
    (lookup : ∀v,environment.lookup (names v)=some (scalarPointer (ids v) (types v))) :
    Bindings {state.leaveScope scope environment with scope:=restore} names types ids owners values := by
  refine ⟨lookup,?_,h.distinct,h.bound⟩
  intro v
  refine ⟨(h.slots v).storable,?_⟩
  change (state.objects (ids v)).map _=_
  rw [(h.slots v).object]
  simp [scalarObject,(different v).symm]

#print axioms Bindings.declare
#print axioms Bindings.store
#print axioms Bindings.leave
end RH080Next.FFTPV.ProductInner
