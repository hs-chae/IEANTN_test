/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WindowExecution

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RH080Next.WindowPV.Execution

/-- Complete fixed-input execution of the actual parsed C function. This is
kernel evaluation of the checked C statement interpreter, not native_decide,
and not an axiom inferred from stdout. All checked word side conditions must
succeed for the statement to reduce to `some`. -/
theorem actual_component_height :
    call 10000 "component_height_numerator" []=some 1146154494119977 := by
  decide +kernel

#print axioms actual_component_height
end RH080Next.WindowPV.Execution
