/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import ScopedC.Restricted

namespace ScopedC.Scalar
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Only ordinary C integer values. Arbitrary precision runtime objects are
separate values: they must never be truncated to a machine integer. -/
structure IntType where
  signed : Bool
  width : Nat
  deriving DecidableEq, Repr

def modulus (t : IntType) : Int := 2 ^ t.width
def lower (t : IntType) : Int := if t.signed then -(2 ^ (t.width - 1)) else 0
def upper (t : IntType) : Int :=
  if t.signed then 2 ^ (t.width - 1) else modulus t
def InRange (t : IntType) (n : Int) : Prop :=
  0 < t.width ∧ lower t ≤ n ∧ n < upper t
instance (t : IntType) (n : Int) : Decidable (InRange t n) := by
  unfold InRange
  infer_instance

structure Value where
  type : IntType
  number : Int
  deriving DecidableEq, Repr

/-- Unsigned arithmetic follows C modular arithmetic. Signed overflow is a
rejected execution, never an assumed wraparound. -/
def make (t : IntType) (n : Int) : Option Value :=
  if t.width = 0 then none
  else if t.signed then
    if InRange t n then some ⟨t,n⟩ else none
  else some ⟨t,n % modulus t⟩

def checked (t : IntType) (n : Int) : Option Value :=
  if InRange t n then some ⟨t,n⟩ else none

def boolean (p : Bool) : Value := ⟨⟨true,32⟩,if p then 1 else 0⟩
def truth (v : Value) : Bool := v.number != 0

/-- The used subset has standard int/unsigned and explicitly sized _BitInt.
Ranks at an equal width may differ, but never change the resulting value
type in these selected operations. No floating or enumeration types occur. -/
def promote (t : IntType) : IntType :=
  if t.width < 32 then ⟨true,32⟩ else t

def common (left right : IntType) : IntType :=
  let a := promote left
  let b := promote right
  if a.signed = b.signed then ⟨a.signed,max a.width b.width⟩
  else if a.signed then
    if b.width ≥ a.width then ⟨false,b.width⟩ else a
  else if a.width ≥ b.width then ⟨false,a.width⟩ else b

def cast (t : IntType) (v : Value) : Option Value := make t v.number

/-- C signed division truncates toward zero. This deliberately differs from
Lean's Euclidean integer division on negative operands. -/
def binary (op : String) (a b : Value) : Option Value := do
  if !(InRange a.type a.number) || !(InRange b.type b.number) then none else
  let t := common a.type b.type
  let x ← cast t a
  let y ← cast t b
  if op == "+" then make t (x.number+y.number)
  else if op == "-" then make t (x.number-y.number)
  else if op == "*" then make t (x.number*y.number)
  else if op == "/" then
    if y.number = 0 then none
    else make t (Int.tdiv x.number y.number)
  else if op == "%" then
    if y.number = 0 then none
    else if t.signed && x.number = lower t && y.number = -1 then none
    else make t (Int.tmod x.number y.number)
  else if op == "<<" then
    if 0 ≤ y.number ∧ y.number < t.width then
      if t.signed && x.number < 0 then none
      else make t (x.number * 2 ^ y.number.toNat)
    else none
  else if op == ">>" then
    if 0 ≤ y.number ∧ y.number < t.width ∧ 0 ≤ x.number then
      make t (x.number / 2 ^ y.number.toNat)
    else none
  else if op == "<" then some (boolean (x.number < y.number))
  else if op == "<=" then some (boolean (x.number ≤ y.number))
  else if op == ">" then some (boolean (x.number > y.number))
  else if op == ">=" then some (boolean (x.number ≥ y.number))
  else if op == "==" then some (boolean (x.number == y.number))
  else if op == "!=" then some (boolean (x.number != y.number))
  else none

theorem checked_exact {t : IntType} {n : Int} (h : InRange t n) :
    checked t n = some ⟨t,n⟩ := by simp [checked,h]

theorem signed_exact {t : IntType} {n : Int} (hs : t.signed = true)
    (h : InRange t n) : make t n = some ⟨t,n⟩ := by
  have hw : t.width ≠ 0 := Nat.ne_of_gt h.1
  simp [make,hw,hs,h]

theorem unsigned_exact {t : IntType} {n : Int} (hs : t.signed = false)
    (h : InRange t n) : make t n = some ⟨t,n⟩ := by
  have hw : t.width ≠ 0 := Nat.ne_of_gt h.1
  have hn : 0 ≤ n := by simpa [lower,hs] using h.2.1
  have hm : n < modulus t := by simpa [upper,hs] using h.2.2
  simp [make,hw,hs,Int.emod_eq_of_lt hn hm]

theorem make_exact {t : IntType} {n : Int} (h : InRange t n) :
    make t n = some ⟨t,n⟩ := by
  cases hs : t.signed
  · exact unsigned_exact hs h
  · exact signed_exact hs h

theorem cast_same {v : Value} (h : InRange v.type v.number) :
    cast v.type v = some v := by
  cases v
  exact make_exact h

theorem signed_division_smoke :
    binary "/" ⟨⟨true,32⟩,-7⟩ ⟨⟨true,32⟩,3⟩ =
      some ⟨⟨true,32⟩,-2⟩ := by decide +kernel

theorem negative_remainder_smoke :
    binary "%" ⟨⟨true,32⟩,-7⟩ ⟨⟨true,32⟩,3⟩ =
      some ⟨⟨true,32⟩,-1⟩ := by decide +kernel

theorem signed_overflow_rejected :
    binary "+" ⟨⟨true,32⟩,2147483647⟩ ⟨⟨true,32⟩,1⟩ = none := by
  decide +kernel

#print axioms make_exact
#print axioms signed_division_smoke
#print axioms signed_overflow_rejected
end ScopedC.Scalar
