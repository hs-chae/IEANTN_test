/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Tactic

namespace ScopedNumerical

/-- Erasure of the source's sign/magnitude record; Nat heap ownership is separate. -/
structure Signed where
  mag : Nat
  neg : Bool
  deriving DecidableEq, Repr

namespace Signed

def value (a : Signed) : Int := if a.neg then -(a.mag : Int) else a.mag
def make (mag : Nat) (neg : Bool) : Signed := ⟨mag, if mag = 0 then false else neg⟩
def negated (a : Signed) : Signed := make a.mag (!a.neg)
def add (a b : Signed) : Signed :=
  if a.neg = b.neg then make (a.mag+b.mag) a.neg
  else if b.mag ≤ a.mag then make (a.mag-b.mag) a.neg
  else make (b.mag-a.mag) b.neg
def mul (a b : Signed) : Signed := make (a.mag*b.mag) (a.neg != b.neg)

@[simp] theorem make_mag (m : Nat) (s : Bool) : (make m s).mag = m := rfl
@[simp] theorem value_make (m : Nat) (s : Bool) :
    (make m s).value = if s then -(m : Int) else m := by
  by_cases h : m = 0 <;> simp [make, value, h]
@[simp] theorem natAbs_value (a : Signed) : a.value.natAbs = a.mag := by
  cases h : a.neg <;> simp [value, h]
@[simp] theorem value_negated (a : Signed) : a.negated.value = -a.value := by
  unfold negated
  rw [value_make]
  cases h : a.neg <;> simp [value, h]
@[simp] theorem value_add (a b : Signed) : (add a b).value = a.value+b.value := by
  cases ha : a.neg <;> cases hb : b.neg <;>
    simp only [add, ha, hb, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
  all_goals try split_ifs
  all_goals simp only [value_make, Bool.false_eq_true, ↓reduceIte]
  all_goals simp only [value, ha, hb, Bool.false_eq_true, ↓reduceIte]
  all_goals omega
@[simp] theorem value_mul (a b : Signed) : (mul a b).value = a.value*b.value := by
  unfold mul
  rw [value_make]
  cases ha : a.neg <;> cases hb : b.neg <;>
    simp [value, ha, hb, Int.natCast_mul]

end Signed

/-- Exact rational represented by source sign/magnitude fields. -/
structure Rational where
  num : Signed
  den : Nat
  deriving DecidableEq, Repr

namespace Rational

def value (q : Rational) : Rat := (q.num.value : Rat)/(q.den : Rat)
def ofRat (q : Rat) : Rational :=
  ⟨Signed.make q.num.natAbs (decide (q.num < 0)), q.den⟩

@[simp] theorem value_ofRat (q : Rat) : (ofRat q).value = q := by
  have hs : (Signed.make q.num.natAbs (decide (q.num < 0))).value = q.num := by
    simp only [Signed.value_make, decide_eq_true_eq]
    split_ifs with h
    · omega
    · omega
  simp only [value, ofRat, hs]
  exact Rat.num_div_den q

/-- Field equality used by source `qm`: denominator is nonzero and gcd reduced. -/
def Normalized (q : Rational) : Prop :=
  0 < q.den ∧ q.num.mag.Coprime q.den ∧ (q.num.mag = 0 → q.num.neg = false)

theorem ofRat_normalized (q : Rat) : (ofRat q).Normalized := by
  refine ⟨q.den_pos, ?_, ?_⟩
  · simpa [ofRat] using q.reduced
  · intro h
    simp only [ofRat, Signed.make_mag] at h
    simp [ofRat, Signed.make, h]

end Rational

end ScopedNumerical
