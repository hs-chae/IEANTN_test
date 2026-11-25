/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RH080.SineBridge

def sineStep (z : Nat) (state : Nat × Nat × Nat) (i : Nat) : Nat × Nat × Nat :=
  let n := i+1
  let next := ((state.1*z/1000000000)*z/1000000000) / ((2*n)*(2*n+1))
  if n%2=0 then (next,state.2.1+next,state.2.2)
  else (next,state.2.1,state.2.2+next)

def sineFixed (r : Nat) : Nat :=
  let z := 3141592654*r/256
  let state := (List.range 8).foldl (sineStep z) (z,z,0)
  state.2.1-state.2.2

def polyQ (x : ℚ) : ℚ :=
  x - x^3/6 + x^5/120 - x^7/5040 + x^9/362880 - x^11/39916800 +
  x^13/6227020800 - x^15/1307674368000 + x^17/355687428096000

end RH080.SineBridge
