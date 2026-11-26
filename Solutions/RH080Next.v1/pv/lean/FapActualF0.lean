/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapExecution
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FapPV.Execution

/-- Complete actual parsed-source execution; no stdout premise or native execution axiom. -/
theorem actual_f0_numerator :
    call 10000 "f0_numerator" []=some 799999999999990000 := by
  decide +kernel

#print axioms actual_f0_numerator
end RH080Next.FapPV.Execution
