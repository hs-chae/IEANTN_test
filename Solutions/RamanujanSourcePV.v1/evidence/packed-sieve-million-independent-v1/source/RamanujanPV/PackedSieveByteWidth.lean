/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveByteCount

/-! Byte padding introduces no additional set bits. These are exact generic
arithmetic/cardinality theorems, without a numerical count or source-PV claim. -/
namespace RamanujanPV.PackedSieveByteWidth
open Finset PackedSieveKernel PackedSieveByteCount
set_option autoImplicit false
set_option maxHeartbeats 0

theorem primeBits_support (lo count i : Nat) (hi : count ≤ i) :
    (primeBits lo count).testBit i = false := by
  simp [primeBits, Nat.testBit_ldiff, show ¬i < count by omega]

theorem lowCount_of_zero_above (count width bits : Nat) (hwidth : count ≤ width)
    (hbits : ∀ i, count ≤ i → bits.testBit i = false) :
    lowCount width bits = lowCount count bits := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hwidth
  unfold lowCount
  rw [sum_range_add]
  have hz : (∑ i ∈ range extra, if bits.testBit (count+i) then 1 else 0) = (0 : Nat) := by
    apply sum_eq_zero
    intro i _
    rw [hbits (count+i) (by omega)]
    rfl
  rw [hz, Nat.add_zero]

theorem byteCount_exact_width (lo count bytes : Nat) (hwidth : count ≤ 8*bytes) :
    byteCount bytes (primeBits lo count) = lowCount count (primeBits lo count) := by
  rw [byteCount_correct]
  exact lowCount_of_zero_above count (8*bytes) _ hwidth (primeBits_support lo count)

theorem byteCount_ceil_width (lo count : Nat) :
    byteCount ((count+7)/8) (primeBits lo count) = lowCount count (primeBits lo count) := by
  apply byteCount_exact_width
  have hm := Nat.mod_lt (count+7) (by decide : 0 < 8)
  have hd := Nat.mod_add_div (count+7) 8
  omega

theorem lowCount_eq_card (width bits : Nat) :
    lowCount width bits = ((range width).filter (fun i => bits.testBit i = true)).card := by
  simp [lowCount, Finset.sum_boole]

#print axioms primeBits_support
#print axioms lowCount_of_zero_above
#print axioms byteCount_exact_width
#print axioms byteCount_ceil_width
#print axioms lowCount_eq_card
end RamanujanPV.PackedSieveByteWidth
