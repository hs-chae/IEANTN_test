/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyC.Header
namespace SynergyC.Word512
open ScopedC
set_option autoImplicit false
set_option maxHeartbeats 0

def type : Scalar.IntType := ⟨false,512⟩
def Range (n : Int) : Prop := 0 ≤ n ∧ n < 2^512
def word (n : Int) : Scalar.Value := ⟨type,n⟩
def value (n : Int) : Machine.Value := .integer (word n)
theorem range_scalar {n : Int} (hn : Range n) : Scalar.InRange type n := by
  simpa [Range,Scalar.InRange,type,Scalar.lower,Scalar.upper,Scalar.modulus] using hn

theorem cast_scalar {n : Int} (hn : Range n) : Scalar.cast type (word n) = some (word n) := by
  exact Scalar.cast_same (v:=word n) (range_scalar hn)

theorem cast_word (s : Machine.State) {n : Int} (hn : Range n) :
    Machine.castValue Header.layout s 100 "U" (value n) = some (value n) := by
  change ((Scalar.cast type (word n)) >>= fun v => some (Machine.Value.integer v)) = some (value n)
  rw [cast_scalar hn]
  rfl

theorem word_add {a b : Int} (ha : Range a) (hb : Range b) (hab : Range (a+b)) :
    Scalar.binary "+" (word a) (word b) = some (word (a+b)) := by
  have ha' := range_scalar ha
  have hb' := range_scalar hb
  have hc := Scalar.make_exact (range_scalar hab)
  simp only [word,Scalar.binary,ha',hb',decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type (word b); Scalar.make type (x.number+y.number)) = _
  rw [cast_scalar ha,cast_scalar hb]
  exact hc

theorem word_sub {a b : Int} (ha : Range a) (hb : Range b) (hab : b ≤ a) :
    Scalar.binary "-" (word a) (word b) = some (word (a-b)) := by
  have ha' := range_scalar ha
  have hb' := range_scalar hb
  have hc : Range (a-b) := by rcases ha with ⟨_,_⟩;rcases hb with ⟨_,_⟩;constructor <;> omega
  have hd := Scalar.make_exact (range_scalar hc)
  simp only [word,Scalar.binary,ha',hb',decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type (word b); Scalar.make type (x.number-y.number)) = _
  rw [cast_scalar ha,cast_scalar hb]
  exact hd

#print axioms cast_word
#print axioms word_add
#print axioms word_sub
end SynergyC.Word512
