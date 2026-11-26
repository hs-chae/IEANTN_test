/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveBindingsFrame
import FFTRecursiveIndexExpressions
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ProductInner

namespace Header

def localIndex : LocalVar → Nat
  | .half => 0 | .status => 1 | .stride => 2 | .j => 3 | .temp => 4

def Active (count : Nat) : LoopVar → Prop
  | .inl _ => True
  | .inr v => localIndex v<count

theorem localIndex_injective : Function.Injective localIndex := by
  intro a b h
  cases a <;> cases b <;> simp_all [localIndex]

theorem loopName_injective : Function.Injective loopName := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => cases a <;> cases b <;> simp_all [loopName,name]
    | inr b => cases a <;> cases b <;> simp_all [loopName,name,localName]
  | inr a =>
    cases b with
    | inl b => cases a <;> cases b <;> simp_all [loopName,name,localName]
    | inr b => cases a <;> cases b <;> simp_all [loopName,localName]

theorem active_step {count : Nat} {next : LocalVar} (hn : localIndex next=count)
    (v : LoopVar) : Active (count+1) v ↔ v=.inr next ∨ Active count v := by
  cases v with
  | inl p => simp [Active]
  | inr v =>
    simp only [Active,Sum.inr.injEq]
    constructor
    · intro h
      by_cases old : localIndex v<count
      · exact Or.inr old
      · exact Or.inl (localIndex_injective (by omega))
    · intro h
      rcases h with rfl | old <;> omega

/-- Only variables already declared by the actual source are present. The
five header locals are introduced one at a time, never assumed initialized. -/
structure PartialBindings {F : Type} (state : State F) (count : Nat)
    (ids : LoopVar → Nat) (owner : Nat) (values : LoopVar → Value) : Prop where
  lookup : ∀v,Active count v → state.environment.lookup (loopName v)=
    some (scalarPointer (ids v) (loopType v))
  slots : ∀v,Active count v → Slot state (ids v) owner (loopType v) (values v)
  distinct : ∀v w,Active count v → Active count w → ids v=ids w → v=w
  bound : owner<state.nextScope

theorem PartialBindings.read {F : Type} {state : State F} {count : Nat}
    {ids : LoopVar → Nat} {owner : Nat} {values : LoopVar → Value}
    (h : PartialBindings state count ids owner values) (v : LoopVar) (hv : Active count v) :
    state.load (scalarPointer (ids v) (loopType v))=some (values v) := (h.slots v hv).read

theorem PartialBindings.declare_next {F : Type} {before after : State F} {count : Nat}
    {ids : LoopVar → Nat} {owner : Nat} {values : LoopVar → Value} {next : LocalVar}
    (h : PartialBindings before count ids owner values) (well : WellScoped before)
    (scope : before.scope=owner) (index : localIndex next=count)
    (d : Declaration before after (localName next) (localType next) (values (.inr next))) :
    PartialBindings after (count+1) (Function.update ids (.inr next) before.nextObject) owner values := by
  have old_active (v : LoopVar) (hv : Active (count+1) v) (different : v≠.inr next) : Active count v :=
    (active_step index v).mp hv |>.resolve_left different
  have old_ne (v : LoopVar) (hv : Active count v) : v≠.inr next := by
    intro same
    subst v
    change localIndex next<count at hv
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro v hv
    by_cases same : v=.inr next
    · subst v
      rw [Function.update_self,d.environment]
      simp [loopName,loopType,List.lookup]
    · have old := old_active v hv same
      have names : loopName v≠localName next := by
        intro eq
        exact same (loopName_injective eq)
      rw [Function.update_of_ne same,d.environment]
      simpa [List.lookup,show (loopName v==localName next)=false by simp [names]] using h.lookup v old
  · intro v hv
    by_cases same : v=.inr next
    · subst v
      rw [Function.update_self]
      simpa [loopType,scope] using d.slot
    · rw [Function.update_of_ne same]
      exact ApplicationBirthFrame.slot_declare_old well (h.slots v (old_active v hv same)) d
  · intro v w hv hw equal
    by_cases vn : v=.inr next
    · subst v
      by_cases wn : w=.inr next
      · exact wn.symm
      · have bound := well.objectIds _ _ (h.slots w (old_active w hw wn)).object
        simp only [Function.update_self,Function.update_of_ne wn] at equal
        omega
    · by_cases wn : w=.inr next
      · subst w
        have bound := well.objectIds _ _ (h.slots v (old_active v hv vn)).object
        simp only [Function.update_self,Function.update_of_ne vn] at equal
        omega
      · simp only [Function.update_of_ne vn,Function.update_of_ne wn] at equal
        exact h.distinct v w (old_active v hv vn) (old_active w hw wn) equal
  · rw [d.nextScope]
    exact h.bound

theorem PartialBindings.complete {F : Type} {state : State F} {ids : LoopVar → Nat}
    {owner : Nat} {values : LoopVar → Value} (h : PartialBindings state 5 ids owner values) :
    Bindings state loopName loopType ids (fun _ => owner) values := by
  have all_active (v : LoopVar) : Active 5 v := by
    cases v with
    | inl p => trivial
    | inr v => cases v <;> simp [Active,localIndex]
  exact ⟨fun v => h.lookup v (all_active v),fun v => h.slots v (all_active v),
    fun v w eq => h.distinct v w (all_active v) (all_active w) eq,fun _ => h.bound⟩

#print axioms PartialBindings.declare_next
#print axioms PartialBindings.complete
end Header
end RH080Next.FFTPV.RecursiveSource
