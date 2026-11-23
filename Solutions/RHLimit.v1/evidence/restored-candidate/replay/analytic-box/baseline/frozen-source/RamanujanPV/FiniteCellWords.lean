/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteScalarRules

/-! Generic typed C arithmetic for the actual seven-word source guard. These
lemmas assume only representability and explicit nonoverflow/positive divisor;
no Ramanujan strict inequality or successful-check premise occurs here. -/
namespace RamanujanPV.FiniteCellWords
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules WideScalar
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

def signedWord (width n : Nat) : FiniteScalarMachine.Value := ⟨⟨true,width⟩,n⟩

lemma signed_valid {width n : Nat} (hw : 0 < width) (hn : n < 2^(width-1)) :
    WideScalar.InRange ⟨true,width⟩ (n:Int) := by
  refine ⟨hw,?_,?_⟩
  · change -(2^(width-1):Int) ≤ (n:Int)
    have h : (0:Int) ≤ n := by exact_mod_cast Nat.zero_le n
    have hp : (0:Int) ≤ 2^(width-1) := by positivity
    omega
  · change (n:Int) < 2^(width-1)
    exact_mod_cast hn

lemma operands64 {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) :
    Operands 64 (word64 a) (word64 b) := by
  exact ⟨scalar_range (by decide) (range_nat ha),scalar_range (by decide) (range_nat hb),
    common_self (by decide),range_nat ha,range_nat hb⟩

lemma operands64signed {a b w : Nat} (ha : a < 2^64) (hw : w=32 ∨ w=64)
    (hb : b < 2^(w-1)) : Operands 64 (word64 a) (signedWord w b) := by
  have wb := signed_valid (by rcases hw with rfl|rfl <;>omega) hb
  have bound : b < 2^64 := by
    rcases hw with rfl|rfl <;>norm_num at hb ⊢ <;>omega
  refine ⟨scalar_range (by decide) (range_nat ha),wb,?_,range_nat ha,range_nat bound⟩
  rcases hw with rfl|rfl <;>rfl

lemma operands128 {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) :
    Operands 128 (word128 a) (word128 b) := by
  exact ⟨scalar_range (by decide) (range_nat ha),scalar_range (by decide) (range_nat hb),
    common_self (by decide),range_nat ha,range_nat hb⟩

lemma operands128_64 {a b : Nat} (ha : a < 2^128) (hb : b < 2^64) :
    Operands 128 (word128 a) (word64 b) := by
  refine ⟨scalar_range (by decide) (range_nat ha),scalar_range (by decide) (range_nat hb),
    by rfl,range_nat ha,range_nat ?_⟩
  exact hb.trans (by norm_num)

lemma operands128signed {a b w : Nat} (ha : a < 2^128) (hw : w=32 ∨ w=64)
    (hb : b < 2^(w-1)) : Operands 128 (word128 a) (signedWord w b) := by
  have wb := signed_valid (by rcases hw with rfl|rfl <;>omega) hb
  have bound : b < 2^128 := by
    rcases hw with rfl|rfl <;>norm_num at hb ⊢ <;>omega
  refine ⟨scalar_range (by decide) (range_nat ha),wb,?_,range_nat ha,range_nat bound⟩
  rcases hw with rfl|rfl <;>rfl

lemma u64_lt {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) :
    WideScalar.binary "<" (word64 a) (word64 b)=some (boolean (decide (a<b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,Int.ofNat_lt] using FiniteScalarRules.lt (by decide) (operands64 ha hb)
lemma u64_le {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) :
    WideScalar.binary "<=" (word64 a) (word64 b)=some (boolean (decide (a≤b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,Int.ofNat_le] using FiniteScalarRules.le (by decide) (operands64 ha hb)
lemma u64_gt {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) :
    WideScalar.binary ">" (word64 a) (word64 b)=some (boolean (decide (b<a))) := by
  rw [binary_reduce (by decide) (operands64 ha hb) ">" (by simp)]
  simp [operation,word64,word128,signedWord,scalarWord,unsignedType,u64,u128]
lemma u64_eq {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) :
    WideScalar.binary "==" (word64 a) (word64 b)=some (boolean (decide (a=b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,beq_iff_eq,Bool.beq_eq_decide_eq] using FiniteScalarRules.eq (by decide) (operands64 ha hb)
lemma u64_ne {a b : Nat} (ha : a < 2^64) (hb : b < 2^64) :
    WideScalar.binary "!=" (word64 a) (word64 b)=some (boolean (decide (a≠b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,bne_iff_ne,bne_eq,Bool.beq_eq_decide_eq] using FiniteScalarRules.ne (by decide) (operands64 ha hb)

lemma u64_signed_lt {a b w : Nat} (ha : a < 2^64) (hw : w=32 ∨ w=64) (hb : b < 2^(w-1)) :
    WideScalar.binary "<" (word64 a) (signedWord w b)=some (boolean (decide (a<b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,Int.ofNat_lt] using FiniteScalarRules.lt (by decide) (operands64signed ha hw hb)
lemma u64_signed_gt {a b w : Nat} (ha : a < 2^64) (hw : w=32 ∨ w=64) (hb : b < 2^(w-1)) :
    WideScalar.binary ">" (word64 a) (signedWord w b)=some (boolean (decide (b<a))) := by
  rw [binary_reduce (by decide) (operands64signed ha hw hb) ">" (by simp)]
  simp [operation,word64,word128,signedWord,scalarWord,unsignedType,u64,u128]
lemma u64_signed_eq {a b w : Nat} (ha : a < 2^64) (hw : w=32 ∨ w=64) (hb : b < 2^(w-1)) :
    WideScalar.binary "==" (word64 a) (signedWord w b)=some (boolean (decide (a=b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,beq_iff_eq,Bool.beq_eq_decide_eq] using FiniteScalarRules.eq (by decide) (operands64signed ha hw hb)

lemma u64_minus_one {a : Nat} (ha : a < 2^64) (positive : 0<a) :
    WideScalar.binary "-" (word64 a) (i32 1)=some (word64 (a-1)) := by
  have result := FiniteScalarRules.sub (by decide) (operands64signed ha (w:=32) (Or.inl rfl) (by decide : 1<2^(32-1)))
    (by
      change Range 64 ((a:Int)-1)
      have h := range_nat ((Nat.sub_le a 1).trans_lt ha)
      simpa only [Int.natCast_sub (by omega : 1≤a),Nat.cast_one] using h)
  simpa [word64,i32,signedWord,scalarWord,unsignedType,u64,u128,Int.natCast_sub (by omega : 1≤a)] using result

lemma u128_mul64 {a b : Nat} (ha : a < 2^128) (hb : b < 2^64) (hab : a*b < 2^128) :
    WideScalar.binary "*" (word128 a) (word64 b)=some (word128 (a*b)) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,Nat.cast_mul] using FiniteScalarRules.mul (by decide) (operands128_64 ha hb) (by simpa [word64,word128,signedWord,Nat.cast_mul] using (range_nat hab))
lemma u128_mul_signed {a b w : Nat} (ha : a < 2^128) (hw : w=32 ∨ w=64)
    (hb : b < 2^(w-1)) (hab : a*b < 2^128) :
    WideScalar.binary "*" (word128 a) (signedWord w b)=some (word128 (a*b)) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,Nat.cast_mul] using FiniteScalarRules.mul (by decide) (operands128signed ha hw hb) (by simpa [word64,word128,signedWord,Nat.cast_mul] using (range_nat hab))
lemma u128_div64 {a b : Nat} (ha : a < 2^128) (hb : b < 2^64) (positive : 0<b) :
    WideScalar.binary "/" (word128 a) (word64 b)=some (word128 (a/b)) := by
  simpa [word64,word128,scalarWord,unsignedType,u64,u128,Int.natCast_div] using FiniteScalarRules.div (by decide) (operands128_64 ha hb)
    (by change (0:Int) < b;exact_mod_cast positive)
lemma u128_lt {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) :
    WideScalar.binary "<" (word128 a) (word128 b)=some (boolean (decide (a<b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,Int.ofNat_lt] using FiniteScalarRules.lt (by decide) (operands128 ha hb)
lemma u128_gt {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) :
    WideScalar.binary ">" (word128 a) (word128 b)=some (boolean (decide (b<a))) := by
  rw [binary_reduce (by decide) (operands128 ha hb) ">" (by simp)]
  simp [operation,word64,word128,signedWord,scalarWord,unsignedType,u64,u128]
lemma u128_ne {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) :
    WideScalar.binary "!=" (word128 a) (word128 b)=some (boolean (decide (a≠b))) := by
  simpa [word64,word128,signedWord,scalarWord,unsignedType,u64,u128,bne_iff_ne,bne_eq,Bool.beq_eq_decide_eq] using FiniteScalarRules.ne (by decide) (operands128 ha hb)

lemma truth_boolean (b : Bool) : WideScalar.truth (boolean b)=b := by cases b <;>decide
lemma boolean_eq_one (b : Bool) : boolean b=i32 1 ↔ b=true := by cases b <;>decide
lemma boolean_eq_zero (b : Bool) : boolean b=i32 0 ↔ b=false := by cases b <;>decide

#print axioms u64_signed_lt
#print axioms u64_minus_one
#print axioms u128_mul64
#print axioms u128_div64
#print axioms u128_lt
#print axioms boolean_eq_one
end RamanujanPV.FiniteCellWords
