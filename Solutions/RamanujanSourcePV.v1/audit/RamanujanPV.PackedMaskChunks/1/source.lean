/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveFold
import RamanujanPV.PackedSievePrimitiveBits

/-! Exact scheduling identities for the frozen composite-divisor OR fold.
This is kernel numerical-proof scheduling, not source PV of a new C program. -/
namespace RamanujanPV.PackedMaskChunks
open PackedSieveKernel PackedSieveFold
set_option autoImplicit false
set_option maxHeartbeats 0

def fold (lo hi base : Nat) (xs : List Nat) (seed : Nat) : Nat :=
  xs.foldl (fun bits j => if base.testBit j then bits else bits ||| divisorMask lo hi (j+2)) seed

theorem fold_seed (lo hi base : Nat) (xs : List Nat) (seed : Nat) :
    fold lo hi base xs seed = seed ||| fold lo hi base xs 0 := by
  apply Nat.eq_of_testBit_eq
  intro bit
  apply Bool.eq_iff_iff.mpr
  simp only [fold,fold_filtered_bit,Nat.testBit_lor,Bool.or_eq_true,
    Nat.zero_testBit,Bool.false_eq_true,false_or]

theorem fold_append (lo hi base : Nat) (xs ys : List Nat) :
    fold lo hi base (xs++ys) 0 = fold lo hi base xs 0 ||| fold lo hi base ys 0 := by
  unfold fold
  rw [List.foldl_append]
  exact fold_seed lo hi base ys _

def rangeMask (lo hi base start length : Nat) : Nat :=
  fold lo hi base (List.range' start length) 0

theorem range_split (lo hi base start left right : Nat) :
    rangeMask lo hi base start (left+right) =
      rangeMask lo hi base start left ||| rangeMask lo hi base (start+left) right := by
  unfold rangeMask
  rw [←List.range'_append_1,fold_append]

def combine (lo hi base : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | start, length::tail => rangeMask lo hi base start length ||| combine lo hi base (start+length) tail

theorem combine_eq_range (lo hi base start : Nat) (lengths : List Nat) :
    combine lo hi base start lengths = rangeMask lo hi base start lengths.sum := by
  induction lengths generalizing start with
  | nil => simp [combine,rangeMask,fold]
  | cons length tail ih =>
    simp only [combine,List.sum_cons,range_split,ih]

theorem composite_as_range (lo count : Nat) :
    compositeMask lo count =
      rangeMask lo (lo+count-1) (allMask 2 (lo+count-1).sqrt) 0 ((lo+count-1).sqrt-1) := by
  simp only [compositeMask,rangeMask,fold,←List.range_eq_range']

theorem composite_from_chunks (lo count : Nat) (lengths : List Nat)
    (coverage : lengths.sum=(lo+count-1).sqrt-1) :
    compositeMask lo count =
      combine lo (lo+count-1) (allMask 2 (lo+count-1).sqrt) 0 lengths := by
  rw [combine_eq_range,coverage,composite_as_range]

#print axioms fold_seed
#print axioms fold_append
#print axioms range_split
#print axioms combine_eq_range
#print axioms composite_as_range
#print axioms composite_from_chunks
end RamanujanPV.PackedMaskChunks
