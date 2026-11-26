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

/-- Complete actual parsed-source execution; no stdout premise or native execution axiom. -/
theorem actual_f0_numerator :
    call 10000 "f0_numerator" []=some 3599999999999999998 := by
  decide +kernel

#print axioms actual_f0_numerator
end RH080Next.WindowPV.Execution
