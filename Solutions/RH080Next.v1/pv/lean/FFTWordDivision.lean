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

private theorem truncDiv_nat (a b : Nat) : truncDiv (a:Int) (b:Int)=(a/b:Nat) := by
  have ha : ¬(a:Int)<0 := by omega
  have hb : ¬(b:Int)<0 := by omega
  simp [truncDiv,ha,hb]

theorem binary64_div (a b : Nat) (ha : a<2^64) (hb : b<2^64) (hpos : 0<b) :
    Integer.binary .div (integer64 a) (integer64 b)=some (integer64 (a/b)) := by
  change (if (Integer.cast .u64 (b:Int)).toInt=0 then none else
    Integer.checked .u64 (truncDiv (Integer.cast .u64 (a:Int)).toInt
      (Integer.cast .u64 (b:Int)).toInt))=_
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt,truncDiv_nat]
  rw [if_neg (by omega)]
  change some (Integer.cast .u64 ((a/b:Nat):Int))=_
  rw [cast64_exact (a/b) (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem binary64_mod (a b : Nat) (ha : a<2^64) (hb : b<2^64) (hpos : 0<b) :
    Integer.binary .mod (integer64 a) (integer64 b)=some (integer64 (a%b)) := by
  change (if (Integer.cast .u64 (b:Int)).toInt=0 then none else
    Integer.checked .u64 ((Integer.cast .u64 (a:Int)).toInt-
      truncDiv (Integer.cast .u64 (a:Int)).toInt (Integer.cast .u64 (b:Int)).toInt*
        (Integer.cast .u64 (b:Int)).toInt))=_
  rw [cast64_exact a ha,cast64_exact b hb,integer64_toInt,integer64_toInt,truncDiv_nat]
  rw [if_neg (by omega)]
  have hm : (a:Int)-(a/b:Nat)*(b:Int)=(a%b:Nat) := by
    have he : (a%b:Int)+(b:Int)*(a/b:Nat)=(a:Int) := by
      exact_mod_cast Nat.mod_add_div a b
    have hc : (a%b:Int)+(a/b:Nat)*(b:Int)=(a:Int) := by nlinarith [he]
    omega

  rw [hm]
  change some (Integer.cast .u64 ((a%b:Nat):Int))=_
  rw [cast64_exact (a%b) (lt_trans (Nat.mod_lt _ hpos) hb)]

#print axioms binary64_div
#print axioms binary64_mod
end RH080Next.FFTPV.WordArrays
