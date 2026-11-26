/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordArrays
import GoldbachDirect.SourceBindings
import GoldbachDirect.SourceLocalOnly
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ApplicationBirthFrame
open GoldbachDirect GoldbachDirect.Semantics
open SourceLocals SourceScalarSlots SourceBindings WordArrays

/-- Application-object frame permitting actual fresh temporary declarations.
The fixed cutoff separates objects present at the application step's entry
from its subsequently allocated locals. Writes below cutoff are explicit. -/
structure Frame {F : Type} (cutoff : Nat) (before after : State F) (writes : List Nat) : Prop where
  well : WellScoped after
  fresh : cutoff≤after.nextObject
  nextObject : before.nextObject≤after.nextObject
  nextScope : before.nextScope≤after.nextScope
  mode : after.mode=before.mode
  foreign : after.foreign=before.foreign
  outside : ∀id,id<cutoff → id∉writes → after.objects id=before.objects id

theorem Frame.refl {F : Type} {state : State F} (cutoff : Nat) (writes : List Nat)
    (well : WellScoped state) (fresh : cutoff≤state.nextObject) : Frame cutoff state state writes :=
  ⟨well,fresh,le_refl _,le_refl _,rfl,rfl,fun _ _ _=>rfl⟩

theorem Frame.trans {F : Type} {a b c : State F} {cutoff : Nat} {writes : List Nat}
    (first : Frame cutoff a b writes) (second : Frame cutoff b c writes) : Frame cutoff a c writes :=
  ⟨second.well,second.fresh,first.nextObject.trans second.nextObject,
    first.nextScope.trans second.nextScope,second.mode.trans first.mode,second.foreign.trans first.foreign,
    fun id old outside => (second.outside id old outside).trans (first.outside id old outside)⟩

theorem enter_frame {F : Type} {state : State F} (cutoff : Nat) (writes : List Nat)
    (well : WellScoped state) (fresh : cutoff≤state.nextObject) : Frame cutoff state state.enterScope writes :=
  ⟨wellScoped_enter well,fresh,le_refl _,by simp [State.enterScope],rfl,rfl,fun _ _ _=>rfl⟩

theorem declare_frame {F : Type} {before after : State F} {ctype : CType} {cname : String}
    {value : Option Value} (cutoff : Nat) (writes : List Nat) (well : WellScoped before)
    (fresh : cutoff≤before.nextObject)
    (run : before.declare ctype cname value=some after) : Frame cutoff before after writes := by
  obtain ⟨scope,ns,no,mode,outside⟩ := SourceLocals.declare_frame run
  refine ⟨wellScoped_declare well run,by omega,by omega,by omega,mode,declare_foreign run,?_⟩
  intro id old absent
  exact outside id (by omega)

theorem store_frame {F : Type} {before after : State F} {pointer : Pointer} {value : Value}
    (cutoff : Nat) (writes : List Nat) (well : WellScoped before) (fresh : cutoff≤before.nextObject)
    (permitted : pointer.object∈writes ∨ cutoff≤pointer.object)
    (run : before.store pointer value=some after) : Frame cutoff before after writes := by
  obtain ⟨environment,mode,scope,ns,no,outside⟩ := SourceLocals.store_frame run
  refine ⟨wellScoped_store well run,by simpa [no] using fresh,by omega,by omega,mode,store_foreign run,?_⟩
  intro id old absent
  apply outside id
  intro eq
  rcases permitted with written | born
  · exact absent (eq ▸ written)
  · omega

/-- Leaving the actual fresh block scope preserves all previous caller objects
outside the declared write set. New temporary slots are freed by the existing
operational lifetime rule; no allocator/runtime applicability is assumed. -/
theorem close_frame {F : Type} {before middle : State F} {cutoff : Nat} {writes : List Nat}
    (well : WellScoped before) (oldBound : cutoff≤before.nextObject)
    (body : Frame cutoff before.enterScope middle writes) :
    Frame cutoff before {middle.leaveScope before.nextScope before.environment with scope:=before.scope} writes := by
  have scopes : before.nextScope+1≤middle.nextScope := body.nextScope
  have current := well.current
  refine ⟨wellScoped_scope (wellScoped_leave body.well _ _) (by change before.scope<middle.nextScope; omega),
    body.fresh,body.nextObject,by change before.nextScope≤middle.nextScope; omega,body.mode,body.foreign,?_⟩
  intro id old absent
  change (middle.objects id).map _=before.objects id
  rw [body.outside id old absent]
  change (before.objects id).map _=before.objects id
  cases present : before.objects id with
  | none => rfl
  | some object =>
    have different : object.storage≠.automatic before.nextScope := by
      intro same
      have hb := well.automatic id object before.nextScope present same
      omega
    simp [different]

theorem slot_declare_old {F : Type} {before after : State F}
    {id owner : Nat} {oldtype newtype : CType} {oldvalue newvalue : Value} {cname : String}
    (well : WellScoped before) (slot : Slot before id owner oldtype oldvalue)
    (declared : Declaration before after cname newtype newvalue) : Slot after id owner oldtype oldvalue := by
  have bound : id<before.nextObject := well.objectIds _ _ slot.object
  exact ⟨slot.storable,by rw [declared.outside id (by omega)]; exact slot.object⟩

/-- Persistent function locals survive declaration of a distinct block-local
name, even though the temporary has a different lifetime owner. -/
theorem locals_declare_old {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat} {values : I → Value}
    {cname : String} {ctype : CType} {value : Value}
    (well : WellScoped before) (locals : Locals before names types ids owner values)
    (different : ∀i,names i≠cname) (declared : Declaration before after cname ctype value) :
    Locals after names types ids owner values := by
  refine ⟨?_,fun i=>slot_declare_old well (locals.slots i) declared,locals.distinct,?_⟩
  · intro i
    rw [declared.environment]
    simpa [List.lookup,show (names i == cname)=false from by simp [different i]] using locals.lookup i
  · rw [declared.nextScope]
    exact locals.bound

theorem array_declare_old {F : Type} {before after : State F}
    {object length : Nat} {data : Nat → Nat} {cname : String} {ctype : CType} {value : Value}
    (well : WellScoped before) (rep : WordArrayRep before object length data)
    (declared : Declaration before after cname ctype value) : WordArrayRep after object length data := by
  have bound : object<before.nextObject := well.objectIds _ _ rep.2.1
  exact ⟨declared.mode.trans rep.1,by rw [declared.outside object (by omega)]; exact rep.2.1,rep.2.2⟩

theorem slot_store_other {F : Type} {before after : State F}
    {id owner : Nat} {ctype : CType} {oldvalue : Value} {pointer : Pointer} {value : Value}
    (slot : Slot before id owner ctype oldvalue) (different : id≠pointer.object)
    (stored : before.store pointer value=some after) : Slot after id owner ctype oldvalue := by
  have outside := (SourceLocals.store_frame stored).2.2.2.2.2
  exact ⟨slot.storable,by rw [outside id different]; exact slot.object⟩

theorem locals_store_other {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids : I → Nat} {owner : Nat} {values : I → Value}
    {pointer : Pointer} {value : Value}
    (locals : Locals before names types ids owner values) (different : ∀i,ids i≠pointer.object)
    (stored : before.store pointer value=some after) : Locals after names types ids owner values := by
  obtain ⟨environment,mode,scope,nextScope,nextObject,outside⟩ := SourceLocals.store_frame stored
  exact ⟨by rw [environment]; exact locals.lookup,
    fun i=>slot_store_other (locals.slots i) (different i) stored,
    locals.distinct,by rw [nextScope]; exact locals.bound⟩

#print axioms close_frame
#print axioms locals_declare_old
#print axioms locals_store_other
end RH080Next.FFTPV.ApplicationBirthFrame
