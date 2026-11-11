/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.CellProgram
import Mathlib
namespace FKSComputationLed.NativeCells
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
/-- Full new continuous-cell numerical provider. All81,314 cells use outward Dyadic
log/exp/Horner arithmetic and the separately proved1e−7 Li Taylor remainder.
No floating scout output or raw numerical accuracy hypothesis is accepted. -/
theorem all_cells_checked : CellProgram.numericGate Input.cells = true := by native_decide
#print axioms all_cells_checked
end FKSComputationLed.NativeCells
