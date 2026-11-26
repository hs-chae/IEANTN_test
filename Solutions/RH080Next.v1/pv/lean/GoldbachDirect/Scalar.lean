import GoldbachDirect.Syntax
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise

/-! The selected LP64, 8-bit-byte C++ source profile. Integer values carry their
machine width. Unsigned operations wrap; invalid shifts/division and signed
overflow have no result. This is not an unbounded-Nat interpretation. -/
namespace GoldbachDirect

inductive IntKind where
  | boolean | char | u8 | u32 | u64 | i32
  deriving Repr, DecidableEq

def IntKind.width : IntKind → Nat
  | .boolean => 1 | .char => 8 | .u8 => 8 | .u32 => 32 | .u64 => 64 | .i32 => 32

def IntKind.signed : IntKind → Bool
  | .char | .i32 => true | _ => false

def IntKind.modulus (kind : IntKind) : Nat := 2^kind.width

def IntKind.promote : IntKind → IntKind
  | .boolean | .char | .u8 => .i32 | other => other

def IntKind.common (left right : IntKind) : IntKind :=
  match left.promote,right.promote with
  | .u64,_ | _,.u64 => .u64
  | .u32,_ | _,.u32 => .u32
  | _,_ => .i32

structure Integer where
  kind : IntKind
  bits : Nat
  deriving Repr, DecidableEq

def Integer.valid (value : Integer) : Prop := value.bits < value.kind.modulus

def Integer.toInt (value : Integer) : Int :=
  if value.kind.signed && decide (2*value.bits ≥ value.kind.modulus) then
    (value.bits : Int) - value.kind.modulus else value.bits

def Integer.cast (kind : IntKind) (value : Int) : Integer :=
  if kind = .boolean then ⟨kind,if value = 0 then 0 else 1⟩
  else ⟨kind,(value % (kind.modulus : Int)).toNat⟩

/-- Signed computation excludes overflow. Conversion into an unsigned type is
modular, as required by the selected C++ integer interpretation. -/
def Integer.checked (kind : IntKind) (value : Int) : Option Integer :=
  if kind.signed && !(decide (-(2^(kind.width-1) : Int) ≤ value ∧ value < 2^(kind.width-1))) then none
  else some (Integer.cast kind value)

def Integer.promoted (value : Integer) : Integer := Integer.cast value.kind.promote value.toInt

def Integer.truth (value : Integer) : Bool := value.toInt != 0

def Integer.boolean (value : Bool) : Integer := ⟨.boolean,if value then 1 else 0⟩

def truncDiv (x y : Int) : Int :=
  let quotient : Int := x.natAbs / y.natAbs
  if (x < 0) != (y < 0) then -quotient else quotient

/-- Strict binary arithmetic. Logical &&/|| are evaluated by short-circuit
source rules, not this eager arithmetic function. -/
def Integer.binary (op : Binary) (left right : Integer) : Option Integer := do
  let kind := IntKind.common left.kind right.kind
  let a := Integer.cast kind left.toInt
  let b := Integer.cast kind right.toInt
  let x := a.toInt
  let y := b.toInt
  match op with
  | .eq => return .boolean (x == y)
  | .ne => return .boolean (x != y)
  | .lt => return .boolean (x < y)
  | .le => return .boolean (x ≤ y)
  | .gt => return .boolean (x > y)
  | .ge => return .boolean (x ≥ y)
  | .add => Integer.checked kind (x+y)
  | .sub => Integer.checked kind (x-y)
  | .mul => Integer.checked kind (x*y)
  | .div => if y = 0 then none else Integer.checked kind (truncDiv x y)
  | .mod => if y = 0 then none else Integer.checked kind (x - truncDiv x y * y)
  | .bitAnd => return ⟨kind,Nat.land a.bits b.bits⟩
  | .bitOr => return ⟨kind,Nat.lor a.bits b.bits⟩
  | .bitXor => return ⟨kind,Nat.xor a.bits b.bits⟩
  | .shl | .shr =>
    let a := left.promoted
    let shift := right.promoted.toInt
    if shift < 0 ∨ shift ≥ a.kind.width then none
    else if op = .shl then return Integer.cast a.kind (a.toInt * (2^shift.toNat : Int))
    else return Integer.cast a.kind (a.toInt / (2^shift.toNat : Int))
  | .logicalAnd | .logicalOr => none

def Integer.unary (op : Unary) (value : Integer) : Option Integer :=
  let value := value.promoted
  match op with
  | .logicalNot => some (.boolean (!value.truth))
  | .negate => Integer.checked value.kind (-value.toInt)
  | .bitNot => some (Integer.cast value.kind (-value.toInt-1))
  | .address | .dereference => none

def CType.integer : CType → Option IntKind
  | .boolean => some .boolean | .char => some .char | .u8 => some .u8
  | .u32 => some .u32 | .u64 | .size | .ull => some .u64
  | .i32 | .int | .cudaError => some .i32
  | .const t => t.integer
  | _ => none

def CType.byteSize : CType → Option Nat
  | .boolean | .char | .u8 => some 1
  | .u32 | .i32 | .int | .cudaError => some 4
  | .u64 | .size | .ull | .pointer _ | .cudaStream => some 8
  | .const t => t.byteSize
  | _ => none

structure Pointer where
  object : Nat
  offset : Nat
  element : CType
  deriving Repr

inductive Value where
  | integer (value : Integer)
  | pointer (value : Pointer)
  | null
  | string (value : String)
  | unit
  deriving Repr

def Value.truth : Value → Option Bool
  | .integer value => some value.truth
  | .pointer _ | .string _ => some true
  | .null => some false
  | .unit => none

def Value.convert (type : CType) (value : Value) : Option Value :=
  match type.integer,value,type with
  | some kind,.integer n,_ => some (.integer (Integer.cast kind n.toInt))
  | _,.null,.pointer _ | _,.null,.cudaStream => some .null
  | _,.integer n,.pointer _ | _,.integer n,.cudaStream => if n.toInt = 0 then some .null else none
  | _,.pointer p,.pointer element => some (.pointer {p with element})
  | _,.pointer p,.cudaStream => some (.pointer p)
  | _,.unit,.void => some .unit
  | _,_,_ => none

/-- The authored sources use decimal integer literals. Unsuffixed small values
have int type; the supported explicit suffixes identify unsigned machine words. -/
def Literal.value : Literal → Option Value
  | .boolean b => some (.integer (.boolean b))
  | .nullPointer => some .null
  | .string value => some (.string value)
  | .character c => if c.toNat < 128 then some (.integer ⟨.char,c.toNat⟩) else none
  | .integer n suffix =>
    if suffix = "" then
      if n < 2^31 then some (.integer ⟨.i32,n⟩) else none
    else if suffix ∈ ["U","u"] then
      if n < 2^32 then some (.integer ⟨.u32,n⟩) else none
    else if suffix ∈ ["ULL","ull","UL","ul"] then
      if n < 2^64 then some (.integer ⟨.u64,n⟩) else none
    else none

end GoldbachDirect
