/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.PVFloorProgram
namespace PVEvolutionA.Recovery.PVFloor
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 theorem checked_boxes : boxesAccepted := by native_decide
 theorem checked_arithmetic : arithmetic := by native_decide
#print axioms checked_boxes
#print axioms checked_arithmetic
end PVEvolutionA.Recovery.PVFloor
