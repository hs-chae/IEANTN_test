/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyHeightC.Initialization
import SynergyHeightC.Bundle

namespace SynergyHeightC.Initialization
open ScopedC ScopedC.Machine
set_option maxHeartbeats 0

/-- This consumes the exact globals projected from the source-bound file
tree. The fourteen-object state is computed by initialization, never supplied
as an application-specific platform assumption. -/
def initializeBoundGlobals : Option State := do
  let st ← Bundle.globals.foldlM initializeOne Machine.empty
  pure {st with env:=[],globals:=st.env}

theorem actual_source_initialization : initializeBoundGlobals = some state := by
  unfold initializeBoundGlobals
  rw [Bundle.globals_exact]
  exact actual_initialization

#print axioms actual_source_initialization
end SynergyHeightC.Initialization
