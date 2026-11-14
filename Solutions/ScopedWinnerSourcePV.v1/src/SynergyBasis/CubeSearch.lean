/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib
namespace SynergyBasis.CubeSearch
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- Ghost fuel bounds iterations, without changing the source midpoint or
branch conditions. Source statement refinement is a separate obligation. -/
def loop : Nat → Nat → Nat → Nat → Nat
  | 0,_,lo,_ => lo
  | fuel+1,n,lo,hi =>
    if lo < hi then
      let mid := lo+(hi-lo)/2+1
      if mid^3 ≤ n then loop fuel n mid hi else loop fuel n lo (mid-1)
    else lo

theorem loop_correct (fuel n lo hi : Nat) (horder : lo ≤ hi)
    (hwidth : hi-lo < 2^fuel) (hl : lo^3 ≤ n) (hu : n < (hi+1)^3) :
    lo ≤ loop fuel n lo hi ∧ loop fuel n lo hi ≤ hi ∧
    (loop fuel n lo hi)^3 ≤ n ∧ n < (loop fuel n lo hi+1)^3 := by
  induction fuel generalizing lo hi with
  | zero =>
    have he : hi=lo := by norm_num at hwidth;omega
    subst hi
    simpa [loop] using And.intro (le_refl lo) (And.intro (le_refl lo) (And.intro hl hu))
  | succ fuel ih =>
    by_cases hlt : lo < hi
    · let mid := lo+(hi-lo)/2+1
      have hm0 : lo < mid := by dsimp [mid];omega
      have hm1 : mid ≤ hi := by dsimp [mid];omega
      have hw : (hi-lo)/2 < 2^fuel := by
        rw [Nat.pow_succ] at hwidth
        omega
      by_cases hm : mid^3 ≤ n
      · have hwm : hi-mid < 2^fuel := by dsimp [mid];omega
        have hh := ih mid hi hm1 hwm hm hu
        simp only [loop,hlt,↓reduceIte]
        change lo ≤ (if mid^3 ≤ n then loop fuel n mid hi else loop fuel n lo (mid-1)) ∧ _
        rw [if_pos hm]
        exact ⟨(le_of_lt hm0).trans hh.1,hh.2⟩
      · have hmw : mid-1-lo < 2^fuel := by dsimp [mid];omega
        have hmo : lo ≤ mid-1 := by omega
        have hmu : n < (mid-1+1)^3 := by
          have he : mid-1+1=mid := by omega
          rw [he]
          exact Nat.lt_of_not_ge hm
        have hh := ih lo (mid-1) hmo hmw hl hmu
        simp only [loop,hlt,↓reduceIte]
        change lo ≤ (if mid^3 ≤ n then loop fuel n mid hi else loop fuel n lo (mid-1)) ∧ _
        rw [if_neg hm]
        exact ⟨hh.1,hh.2.1.trans (by omega),hh.2.2⟩
    · have he : hi=lo := by omega
      subst hi
      simpa [loop] using And.intro (le_refl lo) (And.intro (le_refl lo) (And.intro hl hu))

def scale : Nat := 2^128
def floorCube (n : Nat) : Nat := loop 131 n 0 (4*scale)

theorem floorCube_correct {n : Nat} (hn : n ≤ 16*scale^3) :
    (floorCube n)^3 ≤ n ∧ n < (floorCube n+1)^3 ∧ floorCube n ≤ 4*scale := by
  have h := loop_correct 131 n 0 (4*scale) (by omega)
    (by norm_num [scale]) (by simp)
    (by norm_num [scale] at hn ⊢;omega)
  exact ⟨h.2.2.1,h.2.2.2,h.2.1⟩

theorem all_midpoint_products_fit {mid : Nat} (hm : mid ≤ 4*scale) :
    mid*mid < 2^512 ∧ mid*mid*mid < 2^512 := by
  have hp := Nat.pow_le_pow_left hm 3
  have hp2 := Nat.pow_le_pow_left hm 2
  have hb2 : (4*scale)^2 < 2^512 := by decide +kernel
  have hb3 : (4*scale)^3 < 2^512 := by decide +kernel
  constructor
  · simpa only [pow_two] using hp2.trans_lt hb2
  · calc
      mid*mid*mid = mid^3 := by ring
      _ < 2^512 := hp.trans_lt hb3

#print axioms loop_correct
#print axioms floorCube_correct
#print axioms all_midpoint_products_fit
end SynergyBasis.CubeSearch
