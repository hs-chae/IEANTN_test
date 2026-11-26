import GoldbachDirect.Scalar

namespace GoldbachDirect

inductive Storage where
  | automatic (scope : Nat) | host | device | immutable
  deriving Repr, DecidableEq

inductive Mode where
  | host | device
  deriving Repr, DecidableEq

/-- Scalar cells occupy byte offsets inside one allocation. Uninitialized cells
are absent. Stores invalidate overlapping cells; no out-of-bounds read defaults
an absent value to zero. Allocations have distinct object identities. -/
structure Object where
  extent : Nat
  live : Bool := true
  storage : Storage
  cells : Nat → Option Value

structure State (ForeignState : Type) where
  environment : List (String × Pointer)
  objects : Nat → Option Object
  nextObject : Nat
  scope : Nat
  nextScope : Nat
  mode : Mode := .host
  foreign : ForeignState

def State.accessible {F : Type} (state : State F) (object : Object) : Bool :=
  object.live && match object.storage,state.mode with
    | .device,.host => false
    | .host,.device | .immutable,.device => false
    | _,_ => true

def State.pointerValid {F : Type} (state : State F) (pointer : Pointer) : Bool :=
  match state.objects pointer.object with
  | none => false
  | some object => state.accessible object && decide (pointer.offset ≤ object.extent)

private def valueSize : Value → Nat
  | .integer n => if n.kind = .boolean then 1 else n.kind.width / 8
  | .pointer _ | .null | .string _ => 8
  | .unit => 0


/-- Public scalar-cell width observation; source load/store retain the same
underlying function and representation. -/
def Value.byteSize (value : Value) : Nat := valueSize value

@[simp] theorem stored_u8_width (bits : Nat) : valueSize (.integer ⟨.u8,bits⟩) = 1 := by simp [valueSize, IntKind.width]
@[simp] theorem stored_u32_width (bits : Nat) : valueSize (.integer ⟨.u32,bits⟩) = 4 := by simp [valueSize, IntKind.width]
@[simp] theorem stored_u64_width (bits : Nat) : valueSize (.integer ⟨.u64,bits⟩) = 8 := by simp [valueSize, IntKind.width]
@[simp] theorem stored_pointer_width (pointer : Pointer) : valueSize (.pointer pointer) = 8 := by simp [valueSize]

def State.load {F : Type} (state : State F) (pointer : Pointer) : Option Value := do
  let object ← state.objects pointer.object
  let width ← pointer.element.byteSize
  if !state.accessible object || pointer.offset % width != 0 ||
      pointer.offset+width > object.extent then none
  else
    let value ← object.cells pointer.offset
    if valueSize value != width then none else Value.convert pointer.element value


def State.store {F : Type} (state : State F) (pointer : Pointer) (value : Value) : Option (State F) := do
  let object ← state.objects pointer.object
  let width ← pointer.element.byteSize
  if !state.accessible object || object.storage = .immutable || pointer.offset % width != 0 ||
      pointer.offset+width > object.extent then none
  else
    let converted ← Value.convert pointer.element value
    let next := { object with cells := fun offset =>
      if offset = pointer.offset then some converted
      else (object.cells offset).filter (fun old =>
        !(offset < pointer.offset+width && pointer.offset < offset+valueSize old)) }
    return {state with objects := fun id => if id = pointer.object then some next else state.objects id}

/-- Fresh object birth is a language operation, with an independently specified
storage class/byte extent. Heap/API allocation readiness is not assumed here. -/
def State.allocate {F : Type} (state : State F) (storage : Storage) (extent : Nat)
    (cells : Nat → Option Value := fun _ => none) : Option (Pointer × State F) :=
  if (state.objects state.nextObject).isSome then none else
  let object : Object := ⟨extent,true,storage,cells⟩
  some (⟨state.nextObject,0,.void⟩,
    {state with objects := fun id => if id = state.nextObject then some object else state.objects id
                nextObject := state.nextObject+1})

def State.declare {F : Type} (state : State F) (type : CType) (name : String)
    (value : Option Value) : Option (State F) := do
  let size ← type.byteSize
  let (pointer,next) ← state.allocate (.automatic state.scope) size
  let pointer := {pointer with element := type}
  let next := {next with environment := (name,pointer)::state.environment}
  match value with
  | none => some next
  | some value => next.store pointer value

/-- Scope exit invalidates exactly its automatic objects; malloc/device objects
and caller scopes survive. A retained pointer does not keep a local object live. -/
def State.leaveScope {F : Type} (state : State F) (scope : Nat)
    (environment : List (String × Pointer)) : State F :=
  {state with environment := environment
              objects := fun id => (state.objects id).map (fun object =>
                if object.storage = .automatic scope then {object with live := false} else object)}

def State.enterScope {F : Type} (state : State F) : State F :=
  {state with scope := state.nextScope,nextScope := state.nextScope+1}

def State.pointerAdd {F : Type} (state : State F) (pointer : Pointer) (offset : Int) : Option Pointer := do
  let width ← pointer.element.byteSize
  let result := (pointer.offset : Int) + offset*width
  if result < 0 then none else
    let pointer := {pointer with offset := result.toNat}
    if state.pointerValid pointer then some pointer else none

end GoldbachDirect

namespace GoldbachDirect

@[simp] theorem Value.byteSize_i32 (bits : Nat) : Value.byteSize (.integer ⟨.i32,bits⟩) = 4 := by
  simp [Value.byteSize,valueSize,IntKind.width]

@[simp] theorem Value.byteSize_null : Value.byteSize .null = 8 := by
  simp [Value.byteSize,valueSize]

@[simp] theorem Value.byteSize_boolean (value : Bool) : Value.byteSize (.integer (.boolean value)) = 1 := by
  cases value <;> simp [Value.byteSize,valueSize,Integer.boolean]

end GoldbachDirect
