/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordArrays
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays
open GoldbachDirect

theorem binary64_add (a b : Nat) (ha : a<2^64) (hb : b<2^64) (hab : a+b<2^64) :
    Integer.binary .add (integer64 a) (integer64 b)=some (integer64 (a+b)) := by
  change Integer.checked .u64 ((Integer.cast .u64 (a:Int)).toInt+
    (Integer.cast .u64 (b:Int)).toInt)=some (integer64 (a+b))
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  change some (Integer.cast .u64 ((a:Int)+(b:Int)))=some (integer64 (a+b))
  rw [←Int.natCast_add,cast64_exact (a+b) hab]

theorem binary64_mul (a b : Nat) (ha : a<2^64) (hb : b<2^64) (hab : a*b<2^64) :
    Integer.binary .mul (integer64 a) (integer64 b)=some (integer64 (a*b)) := by
  change Integer.checked .u64 ((Integer.cast .u64 (a:Int)).toInt*
    (Integer.cast .u64 (b:Int)).toInt)=some (integer64 (a*b))
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt]
  change some (Integer.cast .u64 ((a:Int)*(b:Int)))=some (integer64 (a*b))
  rw [←Int.natCast_mul,cast64_exact (a*b) hab]

/-- The exact nested word computation in the source schoolbook multiplication.
All intermediate operations use the existing C integer promotion/wrapping model;
the digit invariant proves wrapping never occurs on this expression. -/
theorem schoolbook_source_word (a b digit carry : Nat)
    (ha : a<1000000000) (hb : b<1000000000)
    (hd : digit<1000000000) (hc : carry<1000000000) :
    (do let p ← Integer.binary .mul (integer64 a) (integer64 b)
        let s ← Integer.binary .add (integer64 digit) p
        Integer.binary .add s (integer64 carry)) =
      some (integer64 (digit+a*b+carry)) := by
  have ht := schoolbook_digit_safe a b digit carry ha hb hd hc
  have ha64 : a<2^64 := by omega
  have hb64 : b<2^64 := by omega
  have hd64 : digit<2^64 := by omega
  have hc64 : carry<2^64 := by omega
  have hp : a*b<2^64 := by omega
  have hs : digit+a*b<2^64 := by omega
  rw [binary64_mul a b ha64 hb64 hp]
  change (do let s ← Integer.binary .add (integer64 digit) (integer64 (a*b))
             Integer.binary .add s (integer64 carry))=_
  rw [binary64_add digit (a*b) hd64 hp hs]
  exact binary64_add (digit+a*b) carry hs hc64 ht

theorem schoolbook_digit_decomposition (a b digit carry : Nat) :
    (digit+a*b+carry)%1000000000+
      1000000000*((digit+a*b+carry)/1000000000)=digit+a*b+carry :=
  Nat.mod_add_div _ _

#print axioms binary64_add
#print axioms binary64_mul
#print axioms schoolbook_source_word
end RH080Next.FFTPV.WordArrays
