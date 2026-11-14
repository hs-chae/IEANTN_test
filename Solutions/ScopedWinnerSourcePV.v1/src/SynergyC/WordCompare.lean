/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SynergyC.Word512
namespace SynergyC.Word512
open ScopedC
set_option autoImplicit false
set_option maxHeartbeats 0

def maxWord : Int := 2^512-1
theorem max_range : Range maxWord := by
  have hp : (0:Int) < 2^512 := pow_pos (by norm_num) _
  unfold Range maxWord
  constructor <;> omega

theorem word_lt_false {a b : Int} (ha : Range a) (hb : Range b) (h : b ≤ a) :
    Scalar.binary "<" (word a) (word b) = some (Scalar.boolean false) := by
  have ha' := range_scalar ha
  have hb' := range_scalar hb
  simp only [word,Scalar.binary,ha',hb',decide_true,Bool.not_true,Bool.false_or,Bool.false_eq_true,↓reduceIte]
  change (do let x ← Scalar.cast type (word a); let y ← Scalar.cast type (word b); pure (Scalar.boolean (x.number < y.number))) = _
  rw [cast_scalar ha,cast_scalar hb]
  simp [word,not_lt.mpr h]

#print axioms word_lt_false
end SynergyC.Word512
