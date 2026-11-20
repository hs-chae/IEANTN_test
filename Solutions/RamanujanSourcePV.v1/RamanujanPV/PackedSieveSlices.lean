/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSievePrefix

/-! Sorted prefix queries reuse disjoint slices of one proved packed bitset.
This is exact kernel arithmetic, not source-PV of a native slice program. -/
namespace RamanujanPV.PackedSieveSlices
open Finset PackedSieveByteCount PackedSieveByteTail PackedSievePrefix
set_option autoImplicit false
set_option maxHeartbeats 0

def sliceBits (start width bits : Nat) : Nat := prefixBits width (bits >>> start)

theorem lowCount_add (start width bits : Nat) :
    lowCount (start+width) bits = lowCount start bits + lowCount width (bits >>> start) := by
  unfold lowCount
  rw [sum_range_add]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Nat.testBit_shiftRight]

theorem slice_count (start width bits : Nat) :
    byteCountFast ((width+7)/8) (sliceBits start width bits) =
      lowCount width (bits >>> start) := by
  exact byteCountFast_prefix width (bits >>> start)

theorem prefix_difference {start next bits : Nat} (advance : start ≤ next) :
    lowCount next bits = lowCount start bits +
      byteCountFast ((next-start+7)/8) (sliceBits start (next-start) bits) := by
  rw [slice_count, ←lowCount_add]
  congr 1
  omega

def checkSlices (bits : Nat) : Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => true
  | start, value, row :: tail =>
    decide (start ≤ row.1 ∧ row.2 = value +
      byteCountFast ((row.1-start+7)/8) (sliceBits start (row.1-start) bits)) &&
    checkSlices bits row.1 row.2 tail

theorem checkSlices_sound {bits start value : Nat} {rows : List (Nat × Nat)}
    (initial : value = lowCount start bits)
    (checked : checkSlices bits start value rows = true) :
    ∀ row ∈ rows, row.2 = lowCount row.1 bits := by
  induction rows generalizing start value with
  | nil => simp
  | cons head tail ih =>
    simp only [checkSlices, Bool.and_eq_true, decide_eq_true_eq] at checked
    obtain ⟨⟨advance, count⟩, rest⟩ := checked
    have actual : head.2 = lowCount head.1 bits := by
      rw [count, initial, ←prefix_difference advance]
    intro row member
    rcases List.mem_cons.mp member with same | later
    · simpa only [same] using actual
    · exact ih actual rest row later

theorem checkSlices_from_zero {bits : Nat} {rows : List (Nat × Nat)}
    (checked : checkSlices bits 0 0 rows = true) :
    ∀ row ∈ rows, row.2 = lowCount row.1 bits := by
  apply checkSlices_sound (by simp [lowCount]) checked

#print axioms lowCount_add
#print axioms slice_count
#print axioms prefix_difference
#print axioms checkSlices_sound
#print axioms checkSlices_from_zero
end RamanujanPV.PackedSieveSlices
