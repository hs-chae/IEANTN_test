/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib

namespace ScopedNumerical

/-- Proof-checker box at scale2^p. This is not an additional C-runtime primitive. -/
structure ProofBox where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

namespace ProofBox
set_option autoImplicit false
set_option maxHeartbeats 0

def scale (p : Nat) : Int := 2^p

def floorDiv (n d : Int) : Int := if 0 < d then n/d else (-n)/(-d)
def ceilDiv (n d : Int) : Int := -floorDiv (-n) d

def literal (p : Nat) (n : Int) (d : Nat) : ProofBox :=
  ⟨floorDiv (n*scale p) (d:Int),ceilDiv (n*scale p) (d:Int)⟩
def add (a b : ProofBox) : ProofBox := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : ProofBox) : ProofBox := ⟨-a.hi,-a.lo⟩
def sub (a b : ProofBox) : ProofBox := add a (neg b)

def min4 (a b c d : Int) : Int := min (min a b) (min c d)
def max4 (a b c d : Int) : Int := max (max a b) (max c d)
def mul (p : Nat) (a b : ProofBox) : ProofBox :=
  ⟨floorDiv (min4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)) (scale p),
    ceilDiv (max4 (a.lo*b.lo) (a.lo*b.hi) (a.hi*b.lo) (a.hi*b.hi)) (scale p)⟩
def inv (p : Nat) (a : ProofBox) : ProofBox :=
  ⟨floorDiv ((scale p)^2) a.hi,ceilDiv ((scale p)^2) a.lo⟩
def min (a b : ProofBox) : ProofBox := ⟨Min.min a.lo b.lo,Min.min a.hi b.hi⟩
def max (a b : ProofBox) : ProofBox := ⟨Max.max a.lo b.lo,Max.max a.hi b.hi⟩
def abs (a : ProofBox) : ProofBox :=
  if 0 ≤ a.lo then a else if a.hi ≤ 0 then neg a
  else ⟨0,Max.max (-a.lo) a.hi⟩
/-- Ordinary recursive multiplication, not binary powering. Soundness is uniform in n. -/
def pow (p : Nat) (a : ProofBox) : Nat → ProofBox
  | 0 => literal p 1 1
  | n+1 => mul p a (pow p a n)

def Contains (p : Nat) (a : ProofBox) (x : Rat) : Prop :=
  (a.lo:Rat) ≤ x*(scale p:Rat) ∧ x*(scale p:Rat) ≤ (a.hi:Rat)

def roundsFloorTo (p q : Nat) (a : ProofBox) (out : Int) : Bool :=
  decide (q ≤ p) && (floorDiv a.lo (scale (p-q)) == out) &&
    (floorDiv a.hi (scale (p-q)) == out)
def roundsCeilTo (p q : Nat) (a : ProofBox) (out : Int) : Bool :=
  decide (q ≤ p) && (ceilDiv a.lo (scale (p-q)) == out) &&
    (ceilDiv a.hi (scale (p-q)) == out)
def roundsFloor (p : Nat) (a : ProofBox) (out : Int) : Bool := roundsFloorTo p 100 a out
def roundsCeil (p : Nat) (a : ProofBox) (out : Int) : Bool := roundsCeilTo p 100 a out

end ProofBox
end ScopedNumerical
