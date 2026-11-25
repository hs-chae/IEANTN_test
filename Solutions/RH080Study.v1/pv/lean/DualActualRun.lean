/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualExecution
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RH080PV.Execution
/-- Closed execution of the actual parsed uint64 C numerical function, including
all 257 grid points, 20 jumps per nonzero point, and the eight-update sine loop.
Every performed operation must pass the checked integer/zero-divisor guards.
This is a finite fixed-input program result, not an unbounded optimizer theorem. -/
theorem actual_numerical_execution :
    call 1000 "rh_dual_bound" [] = some 1221161 := by decide +kernel
#print axioms actual_numerical_execution
end RH080PV.Execution
