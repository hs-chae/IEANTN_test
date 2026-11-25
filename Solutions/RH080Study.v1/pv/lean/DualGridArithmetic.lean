/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualGridModel
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV.Grid
open Model

def accumulator (k : Nat) : Nat × Nat :=
  (List.range 20).foldl (pointStep k) (0,0)

def approximateNumerator (k : Nat) : ℚ :=
  ((accumulator k).1 - ((accumulator k).2 : ℚ)) / (256*1000000000)

def piLower : ℚ := 3141592653/1000000000
def totalJump : ℚ := 3192/256
def sineError : ℚ := 1/10000000

def absoluteAccumulator (k : Nat) : Nat :=
  let (p,n) := accumulator k
  if n≤p then p-n else n-p

/-- Exact rational leaf linking every nonzero grid point's actual fixed-point
arithmetic to the returned integer enclosure. Pi and sine remain real analytic
objects in the separate bridge; they are not replaced here by rational values. -/
def ArithmeticGridCertificate : Prop := ∀ k : Fin 257, k.val≠0 →
  absoluteAccumulator k.val * 10000000 + 532 * (2*3141592653) ≤
    sampleBound k.val * (2*3141592653) * 10 * k.val

theorem arithmetic_grid_certificate : ArithmeticGridCertificate := by
  unfold ArithmeticGridCertificate
  decide

theorem jump_abs_sum :
    (∑ j ∈ Finset.range 20,
      |((positiveJump (j+1) : ℤ) - negativeJump (j+1))|) = 3192 := by decide

theorem jump_weighted_sum :
    (∑ j ∈ Finset.range 20,
      (((positiveJump (j+1) : ℤ) - negativeJump (j+1))*(j+1))) = 625 := by decide

#print axioms arithmetic_grid_certificate
#print axioms jump_abs_sum
#print axioms jump_weighted_sum
end RH080PV.Grid
