/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTRecursiveLoopBindings
import FFTFixedMultiplyFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ProductInner ApplicationBirthFrame

/-- Actual host-array storage cannot be an automatic source-variable slot.
No arbitrary array/variable separation assumption is needed. -/
theorem array_ne_slot {F : Type} {state : State F} {object size id owner : Nat}
    {data : Nat → Nat} {ctype : CType} {value : Value}
    (array : WordArrayRep state object size data) (slot : Slot state id owner ctype value) : object ≠ id := by
  intro same
  subst id
  have equal := Option.some.inj (array.2.1.symm.trans slot.object)
  have storage := congrArg Object.storage equal
  cases storage

/-- A genuine caller-restoring source helper frame preserves every unaffected
actual typed loop binding, including mixed lifetime owners. -/
theorem bindings_after_call {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids owners : I → Nat} {values : I → Value}
    {writes : List Nat} (h : Bindings before names types ids owners values)
    (well : WellScoped before) (frame : MultiplyCall.CallerFrame before after writes)
    (outside : ∀v, ids v ∉ writes) : Bindings after names types ids owners values := by
  refine ⟨?_,?_,h.distinct,?_⟩
  · intro v
    rw [frame.environment]
    exact h.lookup v
  · intro v
    exact ⟨(h.slots v).storable,
      (frame.frame.outside (ids v) (well.objectIds _ _ (h.slots v).object) (outside v)).trans (h.slots v).object⟩
  · intro v
    exact (h.bound v).trans_le frame.frame.nextScope

/-- Caller frames on actual output/work host buffers automatically leave all
actual automatic loop slots untouched. -/
theorem bindings_after_array_call {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids owners : I → Nat} {values : I → Value}
    {objects : List Nat} {length : Nat → Nat} {data : Nat → Nat → Nat}
    (h : Bindings before names types ids owners values) (well : WellScoped before)
    (arrays : ∀object ∈ objects, WordArrayRep before object (length object) (data object))
    (frame : MultiplyCall.CallerFrame before after objects) : Bindings after names types ids owners values := by
  apply bindings_after_call h well frame
  intro v member
  exact (array_ne_slot (arrays (ids v) member) (h.slots v)) rfl

#print axioms array_ne_slot
#print axioms bindings_after_array_call
end RH080Next.FFTPV.RecursiveSource
