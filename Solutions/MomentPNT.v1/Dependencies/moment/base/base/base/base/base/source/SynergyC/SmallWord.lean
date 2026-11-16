/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalMulExpr

namespace SynergyC.SmallWord
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyC.Word512
set_option autoImplicit false
set_option maxHeartbeats 0

def type : Scalar.IntType := ⟨false,32⟩
def Range (n : Int) : Prop := 0 ≤ n ∧ n < 2^32
def scalar (n : Int) : Scalar.Value := ⟨type,n⟩
def value (n : Int) : Machine.Value := .integer (scalar n)

theorem scalar_range {n : Int} (hn : Range n) : Scalar.InRange type n := by
  simpa [Range,Scalar.InRange,type,Scalar.lower,Scalar.upper,Scalar.modulus] using hn

theorem wide_range {n : Int} (hn : Range n) : Word512.Range n := by
  have h : (2:Int)^32 < 2^512 := by decide +kernel
  exact ⟨hn.1,hn.2.trans h⟩

theorem cast_small (s : State) {n : Int} (hn : Range n) :
    castValue Header.layout s 100 "unsigned" (value n) = some (value n) := by
  change ((Scalar.cast type (scalar n)) >>= fun v => some (Machine.Value.integer v)) = some (value n)
  have same : Scalar.cast type (scalar n) = some (scalar n) :=
    Scalar.cast_same (v:=scalar n) (scalar_range hn)
  rw [same]
  rfl

theorem cast_small_int (s : State) {n : Int} (hn : Range n) :
    castValue Header.layout s 100 "unsigned int" (value n) = some (value n) := by
  change ((Scalar.cast type (scalar n)) >>= fun v => some (Machine.Value.integer v)) = some (value n)
  have same : Scalar.cast type (scalar n) = some (scalar n) :=
    Scalar.cast_same (v:=scalar n) (scalar_range hn)
  rw [same]
  rfl

theorem cast_wide {n : Int} (hn : Range n) :
    Scalar.cast Word512.type (scalar n) = some (Word512.word n) :=
  Scalar.make_exact (Word512.range_scalar (wide_range hn))

theorem wide_div {a n : Int} (ha : Word512.Range a) (hn : Range n) (hn0 : 0 < n) :
    Scalar.binary "/" (Word512.word a) (scalar n) = some (Word512.word (a/n)) := by
  have ha' := Word512.range_scalar ha
  have hn' := scalar_range hn
  have hc := Scalar.make_exact (Word512.range_scalar (Word512.quotient_range ha hn0))
  simp only [Word512.word,scalar,Scalar.binary,ha',hn',decide_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast Word512.type (Word512.word a)
             let y ← Scalar.cast Word512.type (scalar n)
             if y.number=0 then none else Scalar.make Word512.type (Int.tdiv x.number y.number)) = _
  rw [Word512.cast_scalar ha,cast_wide hn]
  simpa [Bind.bind,Option.bind,Word512.word,ne_of_gt hn0,Int.tdiv_eq_ediv_of_nonneg ha.1] using hc

theorem eq_zero {n : Int} (hn : Range n) :
    Scalar.binary "==" (scalar n) MulBody.intZero = some (Scalar.boolean (n==0)) := by
  have hn' := scalar_range hn
  have hzero : Scalar.InRange MulBody.intZero.type MulBody.intZero.number := by decide +kernel
  have castn : Scalar.cast type (scalar n) = some (scalar n) := Scalar.cast_same (v:=scalar n) hn'
  have cast0 : Scalar.cast type MulBody.intZero = some (scalar 0) := by decide +kernel
  simp only [scalar,Scalar.binary,hn',hzero,decide_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (scalar n)
             let y ← Scalar.cast type MulBody.intZero
             pure (Scalar.boolean (x.number==y.number))) = _
  rw [castn,cast0]
  rfl

end SynergyC.SmallWord
