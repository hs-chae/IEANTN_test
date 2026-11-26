import GoldbachDirect.Memory
import GoldbachDirect.KernelScalar

set_option autoImplicit false

namespace GoldbachDirect.SourceLocals

open Kernel

def local64 (object : Nat) : Pointer := ⟨object,0,.u64⟩

theorem declare64_of_convert {F : Type} {before after : State F} (name : String) (value : UInt64)
    (original : Value) (converted : Value.convert .u64 original = some (.integer (integer64 value)))
    (declared : before.declare .u64 name (some original) = some after) :
    after.environment = (name,local64 before.nextObject) :: before.environment ∧
      after.load (local64 before.nextObject) = some (.integer (integer64 value)) ∧
      after.nextObject = before.nextObject + 1 ∧
      (∀ key, key ≠ before.nextObject → after.objects key = before.objects key) := by
  cases fresh : before.objects before.nextObject with
  | some old => simp [State.declare, State.allocate, fresh] at declared
  | none =>
      simp [State.declare, State.allocate, fresh, State.store, State.accessible,
        CType.byteSize, converted] at declared
      cases declared
      refine ⟨rfl,?_,rfl,?_⟩
      · simp [State.load, local64, State.accessible, CType.byteSize, Value.convert, CType.integer]
        exact stored_u64_width value.toNat
      · intro key different
        simp [different]

theorem declare64 {F : Type} {before after : State F} (name : String) (value : UInt64)
    (declared : before.declare .u64 name (some (.integer (integer64 value))) = some after) :
    after.environment = (name,local64 before.nextObject) :: before.environment ∧
      after.load (local64 before.nextObject) = some (.integer (integer64 value)) ∧
      after.nextObject = before.nextObject + 1 ∧
      (∀ key, key ≠ before.nextObject → after.objects key = before.objects key) :=
  declare64_of_convert name value _ (by simp [Value.convert,CType.integer]) declared

/-- A valid scalar store changes no different allocation, and preserves every
language environment/scope field. This is proved from the concrete store. -/
theorem store_frame {F : Type} {before after : State F} {pointer : Pointer} {value : Value}
    (written : before.store pointer value = some after) :
    after.environment = before.environment ∧ after.mode = before.mode ∧
      after.scope = before.scope ∧ after.nextScope = before.nextScope ∧
      after.nextObject = before.nextObject ∧
      (∀ key, key ≠ pointer.object → after.objects key = before.objects key) := by
  cases present : before.objects pointer.object with
  | none => simp [State.store, present] at written
  | some object =>
      cases width : pointer.element.byteSize with
      | none => simp [State.store, present, width] at written
      | some bytes =>
          cases converted : Value.convert pointer.element value with
          | none => simp [State.store, present, width, converted] at written
          | some result =>
              simp [State.store, present, width, converted] at written
              rcases written with ⟨_,rfl⟩
              refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
              intro key different
              simp [different]

theorem load_other_after_store {F : Type} {before after : State F}
    {destination source : Pointer} {value : Value}
    (written : before.store destination value = some after)
    (different : source.object ≠ destination.object) : after.load source = before.load source := by
  obtain ⟨_,mode,_,_,_,objects⟩ := store_frame written
  simp only [State.load, objects source.object different, State.accessible, mode]
  rfl

theorem store64_read {F : Type} {before after : State F} {pointer : Pointer}
    (type : pointer.element = .u64) (value : UInt64)
    (written : before.store pointer (.integer (integer64 value)) = some after) :
    after.load pointer = some (.integer (integer64 value)) := by
  cases present : before.objects pointer.object with
  | none => simp [State.store, present] at written
  | some object =>
      simp [State.store, present, type, CType.byteSize, Value.convert, CType.integer] at written
      rcases written with ⟨⟨⟨⟨accessible,_⟩,aligned⟩,bounded⟩,rfl⟩
      simp [State.load, type, CType.byteSize, State.accessible] at accessible ⊢
      simp_all [Value.convert, CType.integer]
      exact stored_u64_width value.toNat

end GoldbachDirect.SourceLocals
