/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.ArgumentConversion

namespace SynergyC.Word512
open ScopedC
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def bit (b : Bool) : Int := if b then 1 else 0
theorem bit_range (b : Bool) : Range (bit b) := by
  cases b <;> change (0:Int) ≤ _ ∧ _ < 2^512 <;> decide +kernel

theorem remainder_range {a b : Int} (hb : Range b) (hb0 : 0 < b) : Range (a%b) := by
  exact ⟨Int.emod_nonneg a (ne_of_gt hb0),lt_trans (Int.emod_lt_of_pos a hb0) hb.2⟩

theorem word_mod {a b : Int} (ha : Range a) (hb : Range b) (hb0 : 0 < b) :
    Scalar.binary "%" (word a) (word b) = some (word (a%b)) := by
  have ha' := range_scalar ha
  have hb' := range_scalar hb
  have hc := Scalar.make_exact (range_scalar (remainder_range hb hb0 (a:=a)))
  simp only [word,Scalar.binary,ha',hb',decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type (word b)
             if y.number=0 then none
             else if type.signed && x.number=Scalar.lower type && y.number = -1 then none
             else Scalar.make type (Int.tmod x.number y.number)) = _
  rw [cast_scalar ha,cast_scalar hb]
  simpa [Bind.bind,Option.bind,word,type,ne_of_gt hb0,Int.tmod_eq_emod_of_nonneg ha.1] using hc

theorem word_eq_zero {a : Int} (ha : Range a) :
    Scalar.binary "==" (word a) MulBody.intZero = some (Scalar.boolean (a == 0)) := by
  have ha' := range_scalar ha
  have hz : Scalar.InRange MulBody.intZero.type MulBody.intZero.number := by decide +kernel
  have h0 : Range 0 := by change (0:Int) ≤ 0 ∧ 0 < 2^512; decide +kernel
  have hc : Scalar.cast type MulBody.intZero = some (word 0) := Scalar.make_exact (range_scalar h0)
  simp only [word,Scalar.binary,ha',hz,decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type MulBody.intZero
             pure (Scalar.boolean (x.number == y.number))) = _
  rw [cast_scalar ha,hc]
  rfl

theorem cast_boolean (s : Machine.State) (b : Bool) :
    Machine.castValue Header.layout s 100 "U" (Machine.boolean Header.layout b) = some (value (bit b)) := by
  change (do let x ← Scalar.make type (bit b); pure (Machine.Value.integer x)) = _
  rw [Scalar.make_exact (range_scalar (bit_range b))]
  rfl

end SynergyC.Word512
