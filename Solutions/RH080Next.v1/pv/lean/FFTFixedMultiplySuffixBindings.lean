/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixCopy
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner

def extend {I A : Type} (old : I → A) (new : A) : Sum I Unit → A := Sum.elim old (fun _ => new)

/-- A new source declaration adds a real fresh typed slot. Every pre-existing
name, slot and lifetime remains linked to its actual run-time object. -/
theorem bindings_extend_declaration {F I : Type} {before after : State F}
    {names : I → String} {types : I → CType} {ids owners : I → Nat} {values : I → Value}
    {cname : String} {ctype : CType} {value : Value}
    (h : Bindings before names types ids owners values) (well : WellScoped before)
    (different : ∀v, names v ≠ cname) (d : Declaration before after cname ctype value) :
    Bindings after (extend names cname) (extend types ctype) (extend ids before.nextObject)
      (extend owners before.scope) (extend values value) := by
  have old := h.declare well different d
  constructor
  · intro v
    cases v with
    | inl v => exact old.lookup v
    | inr v => simp [extend, d.environment, List.lookup]
  · intro v
    cases v with
    | inl v => exact old.slots v
    | inr v => exact d.slot
  · intro a b same
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (h.distinct same)
      | inr b =>
        have bound := well.objectIds _ _ (h.slots a).object
        exact False.elim (by change ids a = before.nextObject at same;omega)
    | inr a =>
      cases b with
      | inl b =>
        have bound := well.objectIds _ _ (h.slots b).object
        exact False.elim (by change before.nextObject = ids b at same;omega)
      | inr b => cases a;cases b;rfl
  · intro v
    cases v with
    | inl v => exact old.bound v
    | inr v => change before.scope < after.nextScope;rw [d.nextScope];exact well.current

/-- Reindexing preserves actual source bindings; the map must be injective. -/
theorem bindings_reindex {F I J : Type} {state : State F}
    {names : I → String} {types : I → CType} {ids owners : I → Nat} {values : I → Value}
    (h : Bindings state names types ids owners values) (f : J → I) (inj : Function.Injective f) :
    Bindings state (names ∘ f) (types ∘ f) (ids ∘ f) (owners ∘ f) (values ∘ f) :=
  ⟨fun v => h.lookup (f v), fun v => h.slots (f v), h.distinct.comp inj, fun v => h.bound (f v)⟩

/-- Actual allocation frames transport arbitrary unaffected mixed-owner slots. -/
theorem slot_scan_frame {F : Type} {before after : State F} {writes : List Nat}
    {id owner : Nat} {ctype : CType} {value : Value}
    (h : Slot before id owner ctype value) (frame : ScanFrame.Frame before after writes)
    (outside : id ∉ writes) : Slot after id owner ctype value :=
  ⟨h.storable, (frame.outside id outside).trans h.object⟩

/-- Scalar stores exist from the real slot and C conversion. -/
theorem scalar_store_exists {F : Type} {state : State F} {id owner : Nat}
    {ctype : CType} {old : Value} (h : Slot state id owner ctype old)
    (v : Value) (hv : Storable ctype v) : ∃after, state.store (scalarPointer id ctype) v = some after := by
  obtain ⟨ht,present⟩ := h
  have same : old.byteSize=v.byteSize := Option.some.inj (ht.typeWidth.symm.trans hv.typeWidth)
  rw [same] at present
  simp [State.store,scalarPointer,present,scalarObject,State.accessible,hv.typeWidth,hv.converted]

#print axioms bindings_extend_declaration
#print axioms bindings_reindex
#print axioms slot_scan_frame
end RH080Next.FFTPV.MultiplySuffix
