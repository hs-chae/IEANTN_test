import GoldbachDirect.Semantics

/-! Individual standard allocation operations in the selected LP64 C++20
profile. These operations know no prime, request, kernel, or output invariant.
They frame other objects by construction and preserve all lexical variables. -/
namespace GoldbachDirect.PlatformMemory

open Semantics

def sizeArgument : Value → Option Nat
  | .integer value => some (Integer.cast .u64 value.toInt).bits
  | _ => none

def zeroBytes (extent : Nat) (offset : Nat) : Option Value :=
  if offset < extent then some (.integer ⟨.u8, 0⟩) else none

def release {F : Type} (state : State F) (pointer : Pointer) : Option (State F) := do
  match state.objects pointer.object with
  | none => none
  | some object =>
    if pointer.offset != 0 || !object.live || object.storage != .host then none
    else some {state with objects := fun id =>
      if id = pointer.object then some {object with live := false} else state.objects id}

/-- A successful allocation is an ordinary fresh mutable object; failure
returns NULL and creates no object. No numerical contents are assumed. -/
inductive Call (F : Type) : External → List Value → State F → Value → State F → Prop where
  | mallocFailure (state : State F) (argument : Value) (bytes : Nat)
      (size : sizeArgument argument = some bytes) :
      Call F .malloc [argument] state .null state
  | mallocSuccess (argument : Value) (bytes : Nat) (before after : State F) (pointer : Pointer)
      (size : sizeArgument argument = some bytes)
      (born : before.allocate .host bytes = some (pointer, after)) :
      Call F .malloc [argument] before (.pointer pointer) after
  | callocFailure (state : State F) (count width : Value) (elements bytes : Nat)
      (countSize : sizeArgument count = some elements)
      (widthSize : sizeArgument width = some bytes) :
      Call F .calloc [count,width] state .null state
  | callocSuccess (count width : Value) (elements bytes : Nat)
      (before after : State F) (pointer : Pointer)
      (countSize : sizeArgument count = some elements)
      (widthSize : sizeArgument width = some bytes)
      (noOverflow : elements * bytes < 2^64)
      (born : before.allocate .host (elements * bytes) (zeroBytes (elements * bytes)) =
        some (pointer, after)) :
      Call F .calloc [count,width] before (.pointer pointer) after
  | freeNull (state : State F) : Call F .free [.null] state .unit state
  | freeObject (before after : State F) (pointer : Pointer)
      (released : release before pointer = some after) :
      Call F .free [.pointer pointer] before .unit after

theorem allocation_other_object {F : Type} {before after : State F}
    {storage : Storage} {extent : Nat} {cells : Nat → Option Value} {pointer : Pointer}
    (born : before.allocate storage extent cells = some (pointer, after))
    {id : Nat} (different : id ≠ before.nextObject) :
    after.objects id = before.objects id := by
  unfold State.allocate at born
  split_ifs at born with occupied
  dsimp only at born
  obtain ⟨hp, ha⟩ := Prod.mk.inj (Option.some.inj born)
  subst pointer
  subst after
  simp [different]

theorem allocation_identity {F : Type} {before after : State F}
    {storage : Storage} {extent : Nat} {cells : Nat → Option Value} {pointer : Pointer}
    (born : before.allocate storage extent cells = some (pointer, after)) :
    pointer.object = before.nextObject ∧ pointer.offset = 0 ∧
      before.objects pointer.object = none ∧
      after.objects pointer.object = some ⟨extent,true,storage,cells⟩ ∧
      after.environment = before.environment ∧ after.foreign = before.foreign := by
  unfold State.allocate at born
  split_ifs at born with occupied
  dsimp only at born
  obtain ⟨hp, ha⟩ := Prod.mk.inj (Option.some.inj born)
  subst pointer
  subst after
  simp_all

theorem release_other_object {F : Type} {before after : State F} {pointer : Pointer}
    (released : release before pointer = some after) {id : Nat} (different : id ≠ pointer.object) :
    after.objects id = before.objects id ∧ after.environment = before.environment ∧
      after.foreign = before.foreign := by
  unfold release at released
  cases object : before.objects pointer.object with
  | none => simp [object] at released
  | some value =>
    simp only [object] at released
    split_ifs at released
    cases Option.some.inj released
    simp [different]

end GoldbachDirect.PlatformMemory
