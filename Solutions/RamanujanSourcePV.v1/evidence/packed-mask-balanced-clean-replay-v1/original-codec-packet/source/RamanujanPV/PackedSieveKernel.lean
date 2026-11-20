/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.SegmentCheckerMath
import Mathlib.Data.Nat.Bitwise
/-! Experimental deterministic packed sieve. These are executable mathematical
functions. Numerical evaluation alone is NOT a prime-count or source-PV proof;
the geometric-mask/classification/popcount refinement must be proved separately. -/
namespace RamanujanPV.PackedSieveKernel
open SegmentCheckerMath
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def twoPow (k : Nat) : Nat := Nat.shiftLeft 1 k

def geomMask (p m : Nat) : Nat := (twoPow (m*p)-1)/(twoPow p-1)

def divisorMask (lo hi p : Nat) : Nat :=
  let first := firstMultiple lo p
  if first ≤ hi then Nat.shiftLeft (geomMask p ((hi-first)/p+1)) (first-lo) else 0

def allMask (lo hi : Nat) : Nat :=
  (List.range (hi.sqrt-1)).foldl (fun bits j=>bits ||| divisorMask lo hi (j+2)) 0

def compositeMask (lo count : Nat) : Nat :=
  let hi := lo+count-1
  let r := hi.sqrt
  let base := allMask 2 r
  (List.range (r-1)).foldl (fun bits j=>
    if base.testBit j then bits else bits ||| divisorMask lo hi (j+2)) 0

def primeBits (lo count : Nat) : Nat := Nat.ldiff (twoPow count-1) (compositeMask lo count)

/-- Broadword population-count scout. Its generic correctness is a separate
proof obligation; a numerical theorem about this function is not yet π. -/
def swarCount (stages bits : Nat) : Nat :=
  let width := twoPow stages
  let all := twoPow width-1
  (List.range stages).foldl (fun n j=>
    let step := twoPow j
    let mask := all/(twoPow step+1)
    (n &&& mask)+((n >>> step) &&& mask)) bits

def scoutCount (lo count stages : Nat) : Nat := swarCount stages (primeBits lo count)

@[simp] theorem twoPow_eq (n : Nat) : twoPow n=2^n := by
  simp [twoPow,Nat.shiftLeft_eq]

#print axioms twoPow_eq
end RamanujanPV.PackedSieveKernel
