import GoldbachDirect.Scalar
import GoldbachGPU.Segmented.Syntax
import Mathlib.Data.UInt
import Mathlib.Tactic

/-! The machine-word interpretation used by the direct C expressions agrees
with Lean's fixed-width UInt operations. These are arithmetic theorems, not a
compiler correspondence assumption and not a Nat-valued replacement for C. -/
namespace GoldbachDirect.Kernel

open GoldbachGPU.Segmented.Code

def integer32 (v : UInt32) : Integer := ⟨.u32,v.toNat⟩
def integer64 (v : UInt64) : Integer := ⟨.u64,v.toNat⟩

@[simp] theorem toInt32 (v : UInt32) : (integer32 v).toInt = (v.toNat : Int) := rfl
@[simp] theorem toInt64 (v : UInt64) : (integer64 v).toInt = (v.toNat : Int) := rfl

@[simp] theorem cast32_nat (n : Nat) :
    Integer.cast .u32 (n : Int) = integer32 (UInt32.ofNat n) := by
  change (⟨.u32,((n : Int) % ((2^32 : Nat) : Int)).toNat⟩ : Integer) =
    ⟨.u32,n % 2^32⟩
  rw [← Int.natCast_emod]
  rfl

@[simp] theorem cast64_nat (n : Nat) :
    Integer.cast .u64 (n : Int) = integer64 (UInt64.ofNat n) := by
  change (⟨.u64,((n : Int) % ((2^64 : Nat) : Int)).toNat⟩ : Integer) =
    ⟨.u64,n % 2^64⟩
  rw [← Int.natCast_emod]
  rfl

@[simp] theorem cast32_self (v : UInt32) :
    Integer.cast .u32 (integer32 v).toInt = integer32 v := by
  simp

@[simp] theorem cast64_self (v : UInt64) :
    Integer.cast .u64 (integer64 v).toInt = integer64 v := by
  simp

@[simp] theorem checked32 (z : Int) :
    Integer.checked .u32 z = some (Integer.cast .u32 z) := rfl
@[simp] theorem checked64 (z : Int) :
    Integer.checked .u64 z = some (Integer.cast .u64 z) := rfl

@[simp] theorem binary64_add (a b : UInt64) :
    Integer.binary .add (integer64 a) (integer64 b) = some (integer64 (a+b)) := by
  change Integer.checked .u64 ((Integer.cast .u64 (integer64 a).toInt).toInt +
    (Integer.cast .u64 (integer64 b).toInt).toInt) = some (integer64 (a+b))
  rw [cast64_self,cast64_self,toInt64,toInt64,checked64,← Int.natCast_add,cast64_nat]
  congr 1

@[simp] theorem binary64_mul (a b : UInt64) :
    Integer.binary .mul (integer64 a) (integer64 b) = some (integer64 (a*b)) := by
  change Integer.checked .u64 ((Integer.cast .u64 (integer64 a).toInt).toInt *
    (Integer.cast .u64 (integer64 b).toInt).toInt) = some (integer64 (a*b))
  rw [cast64_self,cast64_self,toInt64,toInt64,checked64,← Int.natCast_mul,cast64_nat]
  congr 1

@[simp] theorem cast64_int (z : Int) :
    Integer.cast .u64 z = integer64 (UInt64.ofInt z) := by
  have hb : (z % (2^64 : Int)).toNat < 2^64 := by
    have h0 := Int.emod_nonneg z (by norm_num : (2^64 : Int) ≠ 0)
    have h1 := Int.emod_lt_of_pos z (by norm_num : (0 : Int) < 2^64)
    omega
  change (⟨.u64,(z % (2^64 : Int)).toNat⟩ : Integer) =
    ⟨.u64,(z % (2^64 : Int)).toNat % 2^64⟩
  rw [Nat.mod_eq_of_lt hb]

@[simp] theorem ofInt_toNat64 (a : UInt64) : UInt64.ofInt (a.toNat : Int) = a := by
  apply UInt64.toNat_inj.mp
  change ((a.toNat : Int) % ((2^64 : Nat) : Int)).toNat % 2^64 = a.toNat
  rw [← Int.natCast_emod]
  simp

@[simp] theorem binary64_sub (a b : UInt64) :
    Integer.binary .sub (integer64 a) (integer64 b) = some (integer64 (a-b)) := by
  change Integer.checked .u64 ((Integer.cast .u64 (integer64 a).toInt).toInt -
    (Integer.cast .u64 (integer64 b).toInt).toInt) = some (integer64 (a-b))
  rw [cast64_self,cast64_self,toInt64,toInt64,checked64,cast64_int]
  simp [Int.sub_eq_add_neg,UInt64.sub_eq_add_neg]

@[simp] theorem cast_widen (v : UInt32) :
    Integer.cast .u64 (integer32 v).toInt = integer64 v.toUInt64 := by
  rw [toInt32,cast64_nat,UInt64.ofNat_uInt32ToNat]

@[simp] theorem cast_narrow (v : UInt64) :
    Integer.cast .u32 (integer64 v).toInt = integer32 v.toUInt32 := by simp

@[simp] theorem promoted32 (v : UInt32) : (integer32 v).promoted = integer32 v :=
  cast32_self v
@[simp] theorem promoted64 (v : UInt64) : (integer64 v).promoted = integer64 v :=
  cast64_self v

@[simp] theorem binary32_and (a b : UInt32) :
    Integer.binary .bitAnd (integer32 a) (integer32 b) = some (integer32 (a &&& b)) := by
  change some (⟨.u32,Nat.land (Integer.cast .u32 (integer32 a).toInt).bits
    (Integer.cast .u32 (integer32 b).toInt).bits⟩ : Integer) = _
  rw [cast32_self,cast32_self]
  simp [integer32]

@[simp] theorem binary32_or (a b : UInt32) :
    Integer.binary .bitOr (integer32 a) (integer32 b) = some (integer32 (a ||| b)) := by
  change some (⟨.u32,Nat.lor (Integer.cast .u32 (integer32 a).toInt).bits
    (Integer.cast .u32 (integer32 b).toInt).bits⟩ : Integer) = _
  rw [cast32_self,cast32_self]
  simp [integer32]

@[simp] theorem binary64_eq (a b : UInt64) :
    Integer.binary .eq (integer64 a) (integer64 b) = some (.boolean (a == b)) := by
  change some (Integer.boolean ((Integer.cast .u64 (integer64 a).toInt).toInt ==
    (Integer.cast .u64 (integer64 b).toInt).toInt)) = _
  rw [cast64_self,cast64_self,toInt64,toInt64]
  congr 2
  simp [UInt64.toNat_inj]

@[simp] theorem binary64_lt (a b : UInt64) :
    Integer.binary .lt (integer64 a) (integer64 b) = some (.boolean (decide (a < b))) := by
  change some (Integer.boolean (decide ((Integer.cast .u64 (integer64 a).toInt).toInt <
    (Integer.cast .u64 (integer64 b).toInt).toInt))) = _
  rw [cast64_self,cast64_self,toInt64,toInt64]
  congr 2
  simp [UInt64.lt_iff_toNat_lt]

@[simp] theorem binary32_eq (a b : UInt32) :
    Integer.binary .eq (integer32 a) (integer32 b) = some (.boolean (a == b)) := by
  change some (Integer.boolean ((Integer.cast .u32 (integer32 a).toInt).toInt ==
    (Integer.cast .u32 (integer32 b).toInt).toInt)) = _
  rw [cast32_self,cast32_self,toInt32,toInt32]
  congr 2
  simp [UInt32.toNat_inj]

@[simp] theorem truncDiv_nat (a b : Nat) : truncDiv (a : Int) (b : Int) = (a/b : Nat) := by
  have ha : ¬(a : Int) < 0 := by omega
  have hb : ¬(b : Int) < 0 := by omega
  simp [truncDiv,ha,hb]

@[simp] theorem binary64_div (a b : UInt64) :
    Integer.binary .div (integer64 a) (integer64 b) =
      (evalOp64 .div a b).map integer64 := by
  change (if (Integer.cast .u64 (integer64 b).toInt).toInt = 0 then none else
    Integer.checked .u64 (truncDiv (Integer.cast .u64 (integer64 a).toInt).toInt
      (Integer.cast .u64 (integer64 b).toInt).toInt)) = _
  rw [cast64_self,cast64_self,toInt64,toInt64,truncDiv_nat]
  by_cases zero : b = 0
  · simp [zero,evalOp64]
  · have nz : b.toNat ≠ 0 := by
      intro hz
      exact zero (UInt64.toNat_inj.mp (by simpa using hz))
    have inz : (b.toNat : Int) ≠ 0 := by omega
    rw [ite_eq_right inz,checked64,cast64_nat]
    simp only [evalOp64,ite_eq_right zero,Option.map_some]
    congr 1
    apply congrArg integer64
    simp [UInt64.ofNat_div a.toNat_lt b.toNat_lt]

@[simp] theorem binary64_rem (a b : UInt64) :
    Integer.binary .mod (integer64 a) (integer64 b) =
      (evalOp64 .rem a b).map integer64 := by
  change (if (Integer.cast .u64 (integer64 b).toInt).toInt = 0 then none else
    Integer.checked .u64 ((Integer.cast .u64 (integer64 a).toInt).toInt -
      truncDiv (Integer.cast .u64 (integer64 a).toInt).toInt
        (Integer.cast .u64 (integer64 b).toInt).toInt *
          (Integer.cast .u64 (integer64 b).toInt).toInt)) = _
  rw [cast64_self,cast64_self,toInt64,toInt64,truncDiv_nat]
  have hi : (a.toNat : Int) - (a.toNat/b.toNat : Nat) * (b.toNat : Int) =
      (a.toNat % b.toNat : Nat) := by
    have hn : a.toNat = a.toNat % b.toNat + a.toNat / b.toNat * b.toNat := by
      simpa [Nat.mul_comm] using (Nat.mod_add_div a.toNat b.toNat).symm
    have hc : (a.toNat : Int) = (a.toNat % b.toNat : Nat) +
        (a.toNat / b.toNat : Nat) * (b.toNat : Int) := by exact_mod_cast hn
    omega
  rw [hi]
  by_cases zero : b = 0
  · simp [zero,evalOp64]
  · have nz : b.toNat ≠ 0 := by
      intro hz
      exact zero (UInt64.toNat_inj.mp (by simpa using hz))
    have inz : (b.toNat : Int) ≠ 0 := by omega
    rw [ite_eq_right inz,checked64,cast64_nat]
    simp only [evalOp64,ite_eq_right zero,Option.map_some]
    congr 1
    apply congrArg integer64
    simp [UInt64.ofNat_mod a.toNat_lt b.toNat_lt]

@[simp] theorem binary32_shl (a : UInt32) (amount : UInt64) :
    Integer.binary .shl (integer32 a) (integer64 amount) =
      if amount.toNat < 32 then some (integer32 (a <<< UInt32.ofNat amount.toNat)) else none := by
  change (if (integer64 amount).promoted.toInt < 0 ∨
      (integer64 amount).promoted.toInt ≥ (integer32 a).promoted.kind.width then none else
    some (Integer.cast (integer32 a).promoted.kind
      ((integer32 a).promoted.toInt * (2^(integer64 amount).promoted.toInt.toNat : Int)))) = _
  rw [promoted32,promoted64,toInt64,toInt32]
  by_cases bound : amount.toNat < 32
  · have guard : ¬((amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32) := by omega
    change (if (amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32
      then none else some (Integer.cast .u32 ((a.toNat : Int) * 2^amount.toNat))) = _
    rw [ite_eq_right guard,ite_eq_left bound]
    have hn : (a.toNat : Int) * 2^amount.toNat = ((a.toNat * 2^amount.toNat : Nat) : Int) := by simp
    rw [hn,cast32_nat]
    congr 1
    apply congrArg integer32
    apply UInt32.toNat_inj.mp
    simp [UInt32.toNat_shiftLeft,Nat.mod_eq_of_lt bound,Nat.shiftLeft_eq]
  · have guard : (amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32 := by omega
    change (if (amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32
      then none else _) = _
    rw [ite_eq_left guard,ite_eq_right bound]

@[simp] theorem binary32_shr (a : UInt32) (amount : UInt64) :
    Integer.binary .shr (integer32 a) (integer64 amount) =
      if amount.toNat < 32 then some (integer32 (a >>> UInt32.ofNat amount.toNat)) else none := by
  change (if (integer64 amount).promoted.toInt < 0 ∨
      (integer64 amount).promoted.toInt ≥ (integer32 a).promoted.kind.width then none else
    some (Integer.cast (integer32 a).promoted.kind
      ((integer32 a).promoted.toInt / (2^(integer64 amount).promoted.toInt.toNat : Int)))) = _
  rw [promoted32,promoted64,toInt64,toInt32]
  by_cases bound : amount.toNat < 32
  · have guard : ¬((amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32) := by omega
    change (if (amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32
      then none else some (Integer.cast .u32 ((a.toNat : Int) / 2^amount.toNat))) = _
    rw [ite_eq_right guard,ite_eq_left bound]
    have hn : (a.toNat : Int) / 2^amount.toNat = ((a.toNat / 2^amount.toNat : Nat) : Int) := by simp
    rw [hn,cast32_nat]
    congr 1
    apply congrArg integer32
    apply UInt32.toNat_inj.mp
    have hdiv : a.toNat / 2^amount.toNat < 2^32 :=
      (Nat.div_le_self _ _).trans_lt a.toNat_lt
    simp [UInt32.toNat_shiftRight,Nat.mod_eq_of_lt bound,Nat.shiftRight_eq_div_pow]
    exact hdiv
  · have guard : (amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32 := by omega
    change (if (amount.toNat : Int) < 0 ∨ (amount.toNat : Int) ≥ 32
      then none else _) = _
    rw [ite_eq_left guard,ite_eq_right bound]

end GoldbachDirect.Kernel
