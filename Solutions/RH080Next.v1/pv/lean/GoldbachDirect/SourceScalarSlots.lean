import GoldbachDirect.DeclarationFrame
import GoldbachDirect.PureEval

set_option autoImplicit false

namespace GoldbachDirect.SourceScalarSlots
open Semantics

/-- The selected type conversion and stored width, with no program invariant. -/
structure Storable (type : CType) (value : Value) : Prop where
  typeWidth : type.byteSize = some value.byteSize
  positive : 0 < value.byteSize
  converted : Value.convert type value = some value

def scalarObject (owner bytes : Nat) (value : Value) : Object :=
  ⟨bytes,true,.automatic owner,fun offset => if offset=0 then some value else none⟩

def scalarPointer (id : Nat) (type : CType) : Pointer := ⟨id,0,type⟩

structure Slot {F : Type} (state : State F) (id owner : Nat) (type : CType) (value : Value) : Prop where
  storable : Storable type value
  object : state.objects id = some (scalarObject owner value.byteSize value)

theorem Slot.read {F : Type} {state : State F} {id owner : Nat} {type : CType} {value : Value}
    (slot : Slot state id owner type value) : state.load (scalarPointer id type) = some value := by
  obtain ⟨⟨typeWidth,positive,converted⟩,present⟩ := slot
  change state.objects id = some (scalarObject owner value.byteSize value) at present
  unfold State.load
  rw [show (scalarPointer id type).object = id from rfl,present]
  change (do
    let width ← type.byteSize
    if !state.accessible (scalarObject owner value.byteSize value) || 0 % width != 0 ||
        0+width > value.byteSize then none
    else do
      let read ← some value
      if read.byteSize != width then none else Value.convert type read) = some value
  simp [typeWidth,State.accessible,scalarObject,converted]

structure Declaration {F : Type} (before after : State F) (name : String)
    (type : CType) (value : Value) : Prop where
  environment : after.environment = (name,scalarPointer before.nextObject type)::before.environment
  slot : Slot after before.nextObject before.scope type value
  scope : after.scope = before.scope
  nextScope : after.nextScope = before.nextScope
  nextObject : after.nextObject = before.nextObject+1
  mode : after.mode = before.mode
  outside : ∀ id, id ≠ before.nextObject → after.objects id = before.objects id

theorem declare_storable {F : Type} {before after : State F} {name : String} {type : CType}
    {original value : Value} (storable : Storable type value)
    (converted : Value.convert type original = some value)
    (declared : before.declare type name (some original) = some after) :
    Declaration before after name type value := by
  obtain ⟨typeWidth,positive,self⟩ := storable
  cases fresh : before.objects before.nextObject with
  | some old => simp [State.declare,State.allocate,fresh,typeWidth] at declared
  | none =>
    simp [State.declare,State.allocate,fresh,State.store,State.accessible,
      typeWidth,converted] at declared
    cases declared
    refine ⟨rfl,⟨⟨typeWidth,positive,self⟩,?_⟩,rfl,rfl,rfl,rfl,?_⟩
    · unfold scalarObject
      simp only [↓reduceIte]
    · intro id different
      simp [different]

theorem Slot.store {F : Type} {before after : State F} {id owner : Nat} {type : CType}
    {old value : Value} (slot : Slot before id owner type old)
    (storable : Storable type value)
    (written : before.store (scalarPointer id type) value = some after) :
    Slot after id owner type value := by
  obtain ⟨oldType,oldObject⟩ := slot
  have widthSame : old.byteSize = value.byteSize := Option.some.inj (oldType.typeWidth.symm.trans storable.typeWidth)
  rw [widthSame] at oldObject
  simp [State.store,scalarPointer,oldObject,scalarObject,State.accessible,
    storable.typeWidth,storable.converted] at written
  cases written
  refine ⟨storable,?_⟩
  unfold scalarObject
  simp only [↓reduceIte,Option.some.injEq,Object.mk.injEq]
  refine ⟨trivial,trivial,trivial,?_⟩
  funext offset
  by_cases zero : offset=0 <;> simp [zero]

end GoldbachDirect.SourceScalarSlots
