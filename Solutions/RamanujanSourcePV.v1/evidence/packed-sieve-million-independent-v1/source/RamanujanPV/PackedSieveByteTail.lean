/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveByteWidth

/-! An accumulator variant of the proved exact byte population count. This
changes evaluation order only; it assumes no numerical output. -/
namespace RamanujanPV.PackedSieveByteTail
open PackedSieveKernel PackedSieveByteCount PackedSieveByteWidth
set_option autoImplicit false

def byteCountAcc : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | k+1, bits, acc => byteCountAcc k (bits/256) (acc+byteTable.get (bits%256))

theorem byteCountAcc_eq (k bits acc : Nat) :
    byteCountAcc k bits acc = acc+byteCount k bits := by
  induction k generalizing bits acc with
  | zero => simp [byteCountAcc, byteCount]
  | succ k ih =>
    rw [byteCountAcc, ih, byteCount]
    omega

def byteCountFast (k bits : Nat) : Nat := byteCountAcc k bits 0

theorem byteCountFast_eq (k bits : Nat) : byteCountFast k bits = byteCount k bits := by
  simp [byteCountFast, byteCountAcc_eq]

theorem byteCountFast_correct (k bits : Nat) :
    byteCountFast k bits = lowCount (8*k) bits := by
  rw [byteCountFast_eq, byteCount_correct]

theorem byteCountFast_ceil_width (lo count : Nat) :
    byteCountFast ((count+7)/8) (primeBits lo count) = lowCount count (primeBits lo count) := by
  rw [byteCountFast_eq, byteCount_ceil_width]

#print axioms byteCountAcc_eq
#print axioms byteCountFast_eq
#print axioms byteCountFast_correct
#print axioms byteCountFast_ceil_width
end RamanujanPV.PackedSieveByteTail
