/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DualModel
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace RH080PV.Model
/-- All129source-reachable sine arguments, checked against the actual source AST.
A finite application-domain theorem, not a native execution or an assumed table. -/
theorem actual_sine_source_model : SineSourceExecution := by
  unfold SineSourceExecution
  decide
#print axioms actual_sine_source_model
end RH080PV.Model
