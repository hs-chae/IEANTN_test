/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.FiniteScalarMachine
namespace RamanujanPV.FiniteScalarWords
open FiniteScalarMachine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

def unsignedType (width : Nat) : WideScalar.IntType := ⟨false,width⟩
def scalarWord (width : Nat) (number : Int) : Value := ⟨unsignedType width,number⟩
def Range (width : Nat) (number : Int) : Prop := 0≤number ∧number<2^width

theorem scalar_range {width : Nat} {n : Int} (hw : 0<width) (hn : Range width n) :
    WideScalar.InRange (unsignedType width) n := by
  exact ⟨hw,by simpa [WideScalar.lower,unsignedType] using hn.1,
    by simpa [WideScalar.upper,WideScalar.modulus,unsignedType] using hn.2⟩

theorem make_exact {width : Nat} {n : Int} (hw : 0<width) (hn : Range width n) :
    WideScalar.make (unsignedType width) n=some (scalarWord width n) :=
  WideScalar.make_exact (scalar_range hw hn)

theorem cast_number {width : Nat} (value : Value) (hw : 0<width)
    (hn : Range width value.number) :
    WideScalar.cast (unsignedType width) value=some (scalarWord width value.number) :=
  make_exact hw hn

theorem common_self {width : Nat} (hw : 32≤width) :
    WideScalar.common (unsignedType width) (unsignedType width)=unsignedType width := by
  simp [WideScalar.common,WideScalar.promote,unsignedType,Nat.not_lt.mpr hw]

theorem binary_add {width : Nat} {a b : Int} (hw : 32≤width)
    (ha : Range width a) (hb : Range width b) (hab : Range width (a+b)) :
    WideScalar.binary "+" (scalarWord width a) (scalarWord width b)=
      some (scalarWord width (a+b)) := by
  have wa:=scalar_range (by omega : 0<width) ha
  have wb:=scalar_range (by omega : 0<width) hb
  simp only [WideScalar.binary,scalarWord,wa,wb,decide_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte]
  change (do let x←WideScalar.cast (WideScalar.common (unsignedType width) (unsignedType width)) (scalarWord width a)
             let y←WideScalar.cast (WideScalar.common (unsignedType width) (unsignedType width)) (scalarWord width b)
             WideScalar.make (WideScalar.common (unsignedType width) (unsignedType width)) (x.number+y.number))=_
  rw [common_self hw,cast_number (scalarWord width a) (by omega) ha,
    cast_number (scalarWord width b) (by omega) hb]
  exact make_exact (by omega) hab

theorem binary_mul {width : Nat} {a b : Int} (hw : 32≤width)
    (ha : Range width a) (hb : Range width b) (hab : Range width (a*b)) :
    WideScalar.binary "*" (scalarWord width a) (scalarWord width b)=
      some (scalarWord width (a*b)) := by
  have wa:=scalar_range (by omega : 0<width) ha
  have wb:=scalar_range (by omega : 0<width) hb
  simp only [WideScalar.binary,scalarWord,wa,wb,decide_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte]
  change (do let x←WideScalar.cast (WideScalar.common (unsignedType width) (unsignedType width)) (scalarWord width a)
             let y←WideScalar.cast (WideScalar.common (unsignedType width) (unsignedType width)) (scalarWord width b)
             WideScalar.make (WideScalar.common (unsignedType width) (unsignedType width)) (x.number*y.number))=_
  rw [common_self hw,cast_number (scalarWord width a) (by omega) ha,
    cast_number (scalarWord width b) (by omega) hb]
  exact make_exact (by omega) hab

theorem quotient_range {width : Nat} {a b : Int} (ha : Range width a) (hb : 0<b) :
    Range width (a/b) :=
  ⟨Int.ediv_nonneg ha.1 hb.le,(Int.ediv_le_self b ha.1).trans_lt ha.2⟩

theorem binary_div {width : Nat} {a b : Int} (hw : 32≤width)
    (ha : Range width a) (hb : Range width b) (hb0 : 0<b) :
    WideScalar.binary "/" (scalarWord width a) (scalarWord width b)=
      some (scalarWord width (a/b)) := by
  have wa:=scalar_range (by omega : 0<width) ha
  have wb:=scalar_range (by omega : 0<width) hb
  simp only [WideScalar.binary,scalarWord,wa,wb,decide_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte]
  change (do let x←WideScalar.cast (WideScalar.common (unsignedType width) (unsignedType width)) (scalarWord width a)
             let y←WideScalar.cast (WideScalar.common (unsignedType width) (unsignedType width)) (scalarWord width b)
             if y.number=0 then none else WideScalar.make (WideScalar.common (unsignedType width) (unsignedType width)) (Int.tdiv x.number y.number))=_
  rw [common_self hw,cast_number (scalarWord width a) (by omega) ha,
    cast_number (scalarWord width b) (by omega) hb]
  simpa [Bind.bind,Option.bind,scalarWord,ne_of_gt hb0,Int.tdiv_eq_ediv_of_nonneg ha.1]
    using make_exact (by omega : 0<width) (quotient_range ha hb0)

theorem range_nat {width n : Nat} (hn : n<2^width) : Range width (n:Int) := by
  constructor
  · exact_mod_cast Nat.zero_le n
  · exact_mod_cast hn

theorem word64_cast128 {n : Nat} (hn : n<2^64) :
    WideScalar.cast u128 (word64 n)=some (word128 n) := by
  have h : n<2^128 := hn.trans (by norm_num)
  exact cast_number (word64 n) (by decide : 0<128) (range_nat h)

/-- Lexical scope does not alter a state when no local was introduced. -/
theorem close_scope_self (s : State) : closeScope s s=s := by
  cases s with
  | mk env =>
    congr 1
    funext name
    cases h : env name <;>simp [closeScope,h]

#print axioms binary_add
#print axioms binary_mul
#print axioms binary_div
#print axioms word64_cast128
end RamanujanPV.FiniteScalarWords
