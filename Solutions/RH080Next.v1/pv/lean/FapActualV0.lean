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
theorem actual_first_variation_numerator :
    call 10000 "first_variation_numerator" []=some 14047086942420000 := by
  decide +kernel

#print axioms actual_first_variation_numerator
end RH080Next.FapPV.Execution
