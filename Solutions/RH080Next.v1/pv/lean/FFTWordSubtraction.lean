/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordArithmetic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays
open GoldbachDirect

/-- Exact unsigned source subtraction on its proved nonunderflow domain. -/
theorem binary64_sub (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) (hle : b ≤ a) :
    Integer.binary .sub (integer64 a) (integer64 b) = some (integer64 (a-b)) := by
  change Integer.checked .u64 ((Integer.cast .u64 (a:Int)).toInt -
    (Integer.cast .u64 (b:Int)).toInt) = some (integer64 (a-b))
  rw [cast64_exact a ha, cast64_exact b hb, integer64_toInt, integer64_toInt]
  change some (Integer.cast .u64 ((a:Int)-(b:Int))) = some (integer64 (a-b))
  rw [← Nat.cast_sub hle, cast64_exact (a-b) (lt_of_le_of_lt (Nat.sub_le _ _) ha)]

theorem binary64_lt (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    Integer.binary .lt (integer64 a) (integer64 b) = some (.boolean (decide (a < b))) := by
  change some (Integer.boolean ((Integer.cast .u64 (a:Int)).toInt < (Integer.cast .u64 (b:Int)).toInt)) = _
  rw [cast64_exact a ha, cast64_exact b hb, integer64_toInt, integer64_toInt]
  congr 2
  simp

theorem binary64_eq (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    Integer.binary .eq (integer64 a) (integer64 b) = some (.boolean (decide (a = b))) := by
  change some (Integer.boolean ((Integer.cast .u64 (a:Int)).toInt = (Integer.cast .u64 (b:Int)).toInt)) = _
  rw [cast64_exact a ha, cast64_exact b hb, integer64_toInt, integer64_toInt]
  congr 2
  simp

#print axioms binary64_sub
#print axioms binary64_lt
#print axioms binary64_eq
end RH080Next.FFTPV.WordArrays
