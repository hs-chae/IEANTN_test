/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyC.WordCompare
namespace SynergyC.Word512
open ScopedC
set_option autoImplicit false
set_option maxHeartbeats 0

theorem word_mul {a b : Int} (ha : Range a) (hb : Range b) (hab : Range (a*b)) :
    Scalar.binary "*" (word a) (word b) = some (word (a*b)) := by
  have ha' := range_scalar ha
  have hb' := range_scalar hb
  have hc := Scalar.make_exact (range_scalar hab)
  simp only [word,Scalar.binary,ha',hb',decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type (word b); Scalar.make type (x.number*y.number)) = _
  rw [cast_scalar ha,cast_scalar hb]
  exact hc

theorem quotient_range {a b : Int} (ha : Range a) (hb : 0 < b) : Range (a/b) := by
  rcases ha with ⟨ha0,ha1⟩
  constructor
  · exact Int.ediv_nonneg ha0 hb.le
  · exact (Int.ediv_le_self b ha0).trans_lt ha1

theorem word_div {a b : Int} (ha : Range a) (hb : Range b) (hb0 : 0 < b) :
    Scalar.binary "/" (word a) (word b) = some (word (a/b)) := by
  have ha' := range_scalar ha
  have hb' := range_scalar hb
  have hc := Scalar.make_exact (range_scalar (quotient_range ha hb0))
  simp only [word,Scalar.binary,ha',hb',decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type (word b)
             if y.number=0 then none else Scalar.make type (Int.tdiv x.number y.number)) = _
  rw [cast_scalar ha,cast_scalar hb]
  simpa [Bind.bind,Option.bind,word,ne_of_gt hb0,Int.tdiv_eq_ediv_of_nonneg ha.1] using hc

theorem mul_guard_safe {a b : Int} (ha : 0 < a) (hab : Range (a*b)) :
    b ≤ maxWord/a := by
  apply (Int.le_ediv_iff_mul_le ha).2
  have h := hab.2
  unfold maxWord
  nlinarith

#print axioms word_mul
#print axioms word_div
#print axioms mul_guard_safe
end SynergyC.Word512
