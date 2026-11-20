/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveSource
import RamanujanPV.PackedSieveByteTail

/-! Prefix counts reuse the same proved packed sieve. Truncating the bitset
before byte counting removes partial-byte padding exactly, without a new sieve. -/
namespace RamanujanPV.PackedSievePrefix
open Finset PackedSieveKernel PackedSieveByteCount PackedSieveByteWidth
open QuotientCMachine SegmentMemory QuotientCCell
set_option autoImplicit false
set_option maxHeartbeats 0

def prefixBits (width bits : Nat) : Nat := bits &&& (2^width-1)

theorem prefix_support (width bits i : Nat) (hi : width ≤ i) :
    (prefixBits width bits).testBit i = false := by
  simp [prefixBits, Nat.testBit_and, show ¬i < width by omega]

theorem lowCount_prefix (width bits : Nat) :
    lowCount width (prefixBits width bits) = lowCount width bits := by
  apply sum_congr rfl
  intro i hi
  have hindex : i < width := mem_range.mp hi
  simp [prefixBits, Nat.testBit_and, hindex]

theorem byteCount_prefix (width bits : Nat) :
    byteCount ((width+7)/8) (prefixBits width bits) = lowCount width bits := by
  rw [byteCount_correct]
  have bound : width ≤ 8*((width+7)/8) := by
    have hm := Nat.mod_lt (width+7) (by decide : 0 < 8)
    have hd := Nat.mod_add_div (width+7) 8
    omega
  rw [lowCount_of_zero_above width _ _ bound (prefix_support width bits), lowCount_prefix]

theorem byteCountFast_prefix (width bits : Nat) :
    PackedSieveByteTail.byteCountFast ((width+7)/8) (prefixBits width bits) =
      lowCount width bits := by
  rw [PackedSieveByteTail.byteCountFast_eq, byteCount_prefix]

theorem source_count_at_byte {call : Service} {s : State}
    {lo count capacity cb fb baseValue i : Nat}
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (cap : count ≤ capacity) (apart : cb ≠ fb)
    (owned : Owned s.heap) (scratch : SegmentCInit.Buffer s.heap fb count)
    (inputFlags : FlagsRep s.heap cb count (PackedSieveSource.claims lo count))
    (env : SegmentCFunctionPrefix.Inputs lo (lo+count-1) capacity cb fb s.env)
    (base : SourceExecution (lo-1) baseValue) (index : i < count) :
    SourceExecution (lo+i)
      (baseValue+byteCount ((i+8)/8) (prefixBits (i+1) (primeBits lo count))) := by
  have actual := PackedSieveSource.source_count_at (call := call)
    hlo hcount upper cap apart owned scratch inputFlags env base index
  simpa only [show i+8=(i+1)+7 by omega, byteCount_prefix] using actual

#print axioms prefix_support
#print axioms lowCount_prefix
#print axioms byteCount_prefix
#print axioms byteCountFast_prefix
#print axioms source_count_at_byte
end RamanujanPV.PackedSievePrefix
