/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.Word512

namespace SynergyC.Word512
open ScopedC
set_option autoImplicit false
set_option maxHeartbeats 100000

/-- The actual nonnegative UInt512 result of a small right shift remains in
range. This is integer division, with no floating or truncated oracle. -/
theorem shiftRight_range {n : Int} (hn : Range n) (k : Nat) : Range (n/(2^k:Int)) := by
  exact ⟨Int.ediv_nonneg hn.1 (le_of_lt (pow_pos (by decide : (0:Int)<2) k)),
    (Int.ediv_le_self (2^k) hn.1).trans_lt hn.2⟩

/-- Actual Scalar.binary semantics for the emitU source operands: unsigned
_BitInt(512) x and unsigned-int (64*i), with the original header's widths.
The shift conversion and all range/definedness checks are discharged. -/
theorem word_shiftRight {n : Int} (hn : Range n) (k : Nat) (hk : k<512) :
    Scalar.binary ">>" (word n) ⟨⟨false,32⟩,(k:Int)⟩=
      some (word (n/(2^k:Int))) := by
  have rightRange : Scalar.InRange ⟨false,32⟩ (k:Int) := by
    change 0<32 ∧ 0≤(k:Int) ∧ (k:Int)<2^32
    refine ⟨by decide,Int.natCast_nonneg _,?_⟩
    exact_mod_cast (lt_trans hk (by decide +kernel : 512<2^32))
  have kInt : (k:Int)<512 := by exact_mod_cast hk
  have small : Range (k:Int) := ⟨Int.natCast_nonneg _,lt_trans kInt (by decide +kernel : (512:Int)<2^512)⟩
  have castRight : Scalar.cast type ⟨⟨false,32⟩,(k:Int)⟩=some (word (k:Int)) :=
    Scalar.make_exact (range_scalar small)
  have leftRange:=range_scalar hn
  have result:=Scalar.make_exact (range_scalar (shiftRight_range hn k))
  simp only[Scalar.binary,word,leftRange,rightRange,decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do
    let x←Scalar.cast type (word n)
    let y←Scalar.cast type ⟨⟨false,32⟩,(k:Int)⟩
    if 0≤y.number ∧ y.number<512 ∧ 0≤x.number then
      Scalar.make type (x.number/2^y.number.toNat)
    else none)=_
  rw[cast_scalar hn,castRight]
  simpa only[Bind.bind,Option.bind,word,Int.natCast_nonneg,kInt,hn.1,Int.toNat_natCast,
    and_self,↓reduceIte] using result

theorem binaryValue_shiftRight (s : Machine.State) {n : Int} (hn : Range n) (k : Nat) (hk : k<512) :
    Machine.binaryValue Header.layout s ">>" (value n) (.integer ⟨⟨false,32⟩,(k:Int)⟩)=
      some (value (n/(2^k:Int))) := by
  change (do let x←Scalar.binary ">>" (word n) ⟨⟨false,32⟩,(k:Int)⟩;pure (Machine.Value.integer x))=_
  rw[word_shiftRight hn k hk]
  rfl

end SynergyC.Word512
