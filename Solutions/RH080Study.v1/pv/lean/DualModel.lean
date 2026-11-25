/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualExecution

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080PV.Model

/-- High-level mathematical specification of the actual nine-term, truncating
fixed-point sine routine. The general execution model remains independently
defined by the parsed C statement AST in DualExecution. -/
def sineStep (z : Nat) (state : Nat × Nat × Nat) (i : Nat) : Nat × Nat × Nat :=
  let n := i+1
  let next := ((state.1*z/1000000000)*z/1000000000) / ((2*n)*(2*n+1))
  if n%2=0 then (next,state.2.1+next,state.2.2)
  else (next,state.2.1,state.2.2+next)

def sineFixed (r : Nat) : Nat :=
  let z := 3141592654*r/256
  let state := (List.range 8).foldl (sineStep z) (z,z,0)
  state.2.1-state.2.2

/-- Finite source-domain claim only; no unbounded sine algorithm is asserted. -/
def SineSourceExecution : Prop :=
  ∀ r : Fin 129, Execution.call 1000 "sine_fixed" [r.val] = some (sineFixed r.val)

def positiveJump (j : Nat) : Nat :=
  match j with
  | 4 => 837 | 7 => 251 | 9 => 249 | 11 => 176
  | 15 => 111 | 17 => 82 | 19 => 18 | _ => 0

def negativeJump (j : Nat) : Nat :=
  match j with
  | 5 => 621 | 6 => 129 | 8 => 229 | 10 => 170 | 12 => 119
  | 13 => 23 | 14 => 15 | 16 => 103 | 18 => 59 | _ => 0

def reducedAngle (j k : Nat) : Nat × Bool :=
  let r := j*k%512
  let flipped := 256<r
  let r := if flipped then 512-r else r
  (if 128<r then 256-r else r, flipped)

def pointStep (k : Nat) (state : Nat × Nat) (i : Nat) : Nat × Nat :=
  let j := i+1
  let (r,flipped) := reducedAngle j k
  let sine := sineFixed r
  let a := positiveJump j
  let b := negativeJump j
  if flipped then (state.1+b*sine,state.2+a*sine)
  else (state.1+a*sine,state.2+b*sine)

def sampleBound (k : Nat) : Nat :=
  if k=0 then 1220704
  else
    let (positive,negative) := (List.range 20).foldl (pointStep k) (0,0)
    let absolute := if negative≤positive then positive-negative else negative-positive
    let numerator := ((absolute+255)/256)*256000000
    let denominator := 2*3141592653*k
    (numerator+denominator-1)/denominator+200

def gridMaximum : Nat := ((List.range 257).map sampleBound).foldl max 0

theorem reducedAngle_mem (j k : Nat) : (reducedAngle j k).1 ≤ 128 := by
  have hmod := Nat.mod_lt (j*k) (by decide : 0<512)
  simp only [reducedAngle]
  split <;> split <;> simp_all <;> omega

/-- Pure model diagnostic, kernel evaluated. This is not yet an actual C-AST
execution theorem; the corresponding source execution claim is separate. -/
theorem sineFixed_zero : sineFixed 0 = 0 := by decide

#print axioms sineFixed_zero
end RH080PV.Model
