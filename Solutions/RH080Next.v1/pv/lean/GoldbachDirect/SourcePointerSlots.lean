import GoldbachDirect.SourceSlots

set_option autoImplicit false

namespace GoldbachDirect.SourcePointerSlots
open Semantics

def localPointer (object : Nat) (element : CType) : Pointer := ⟨object,0,.pointer element⟩

def pointerObject (owner : Nat) (value : Pointer) : Object :=
  ⟨8,true,.automatic owner,fun offset => if offset=0 then some (.pointer value) else none⟩

def Slot {F : Type} (state : State F) (id owner : Nat) (value : Pointer) : Prop :=
  state.objects id = some (pointerObject owner value)

theorem convert_typed (value : Pointer) {element : CType} (typed : value.element=element) :
    Value.convert (.pointer element) (.pointer value)=some (.pointer value) := by
  cases value
  simp_all [Value.convert,CType.integer]

theorem read {F : Type} {state : State F} {id owner : Nat} {value : Pointer} {element : CType}
    (slot : Slot state id owner value) (typed : value.element = element) :
    state.load (localPointer id element) = some (.pointer value) := by
  change state.objects id = some (pointerObject owner value) at slot
  simp [State.load,localPointer,slot,pointerObject,State.accessible,CType.byteSize,
    Value.convert,CType.integer]
  cases value
  simp_all

structure Declaration {F : Type} (before after : State F) (name : String) (element : CType)
    (value : Pointer) : Prop where
  environment : after.environment = (name,localPointer before.nextObject element)::before.environment
  slot : Slot after before.nextObject before.scope value
  nextObject : after.nextObject = before.nextObject+1
  scope : after.scope = before.scope
  nextScope : after.nextScope = before.nextScope
  mode : after.mode = before.mode
  foreign : after.foreign = before.foreign
  outside : ∀ id, id ≠ before.nextObject → after.objects id = before.objects id

theorem declare_pointer_of_convert {F : Type} {before after : State F}
    (name : String) (element : CType) (value : Pointer) (original : Value)
    (converted : Value.convert (.pointer element) original = some (.pointer value))
    (declared : before.declare (.pointer element) name (some original) = some after) :
    Declaration before after name element value := by
  cases fresh : before.objects before.nextObject with
  | some old => simp [State.declare,State.allocate,fresh] at declared
  | none =>
      simp [State.declare,State.allocate,fresh,State.store,State.accessible,
        CType.byteSize,converted] at declared
      cases declared
      refine ⟨rfl,?_,rfl,rfl,rfl,rfl,rfl,?_⟩
      · unfold Slot pointerObject
        simp only [↓reduceIte]
      · intro id different
        simp [different]

theorem leave {F : Type} {state : State F} {id owner scope : Nat} {value : Pointer}
    (slot : Slot state id owner value) (different : scope ≠ owner)
    (environment : List (String × Pointer)) (restore : Nat) :
    Slot {state.leaveScope scope environment with scope:=restore} id owner value := by
  change ((state.objects id).map _) = _
  rw [slot]
  simp [pointerObject,different.symm]

theorem store_other {F : Type} {before after : State F} {id owner : Nat} {value : Pointer}
    {pointer : Pointer} {written : Value} (slot : Slot before id owner value)
    (different : id ≠ pointer.object) (run : before.store pointer written = some after) :
    Slot after id owner value :=
  (SourceLocals.store_frame run).2.2.2.2.2 id different |>.trans slot

end GoldbachDirect.SourcePointerSlots
