/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveKernel

/-! The same finite bit difference expressed using primitive AND/XOR operations.
The identity is proved for every input, without a proposed bitmask or count. -/
namespace RamanujanPV.PackedSievePrimitiveBits
open PackedSieveKernel
set_option autoImplicit false

def primitiveBits (lo count : Nat) : Nat :=
  let mask := twoPow count-1
  mask ^^^ (mask &&& compositeMask lo count)

theorem primitiveBits_eq (lo count : Nat) : primitiveBits lo count = primeBits lo count := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [primitiveBits, primeBits, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_ldiff]
  cases (twoPow count-1).testBit i <;> cases (compositeMask lo count).testBit i <;> rfl

#print axioms primitiveBits_eq
end RamanujanPV.PackedSievePrimitiveBits
