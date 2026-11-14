/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NumericSignedMultiplyRefinement

namespace ScopedC.SignedNormalization
open ScopedC.Machine ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Required by the actual sign-first comparison helper: zero has false sign.
Raw negative zero is still a meaningful Signed value for add/mul/negation. -/
def ZeroNormalized (a : Signed) : Prop := a.mag=0 → a.neg=false

theorem make_normalized (n : Nat) (b : Bool) : ZeroNormalized (Signed.make n b) := by
  intro zero
  have h : n=0 := zero
  simp [Signed.make,h]

theorem negated_normalized (a : Signed) : ZeroNormalized a.negated := make_normalized _ _
theorem mul_normalized (a b : Signed) : ZeroNormalized (Signed.mul a b) := make_normalized _ _

theorem add_normalized (a b : Signed) : ZeroNormalized (Signed.add a b) := by
  unfold Signed.add
  split_ifs <;> exact make_normalized _ _

def Represents (s : State) (v : Value) (a : Signed) : Prop :=
  NumericRepresentation.signed s v=some a ∧ ZeroNormalized a

def RationalZeroNormalized (q : Rational) : Prop := ZeroNormalized q.num

end ScopedC.SignedNormalization
