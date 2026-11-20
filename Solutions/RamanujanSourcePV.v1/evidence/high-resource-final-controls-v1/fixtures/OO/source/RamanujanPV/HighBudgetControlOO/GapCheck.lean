/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.HighBudgetControlOO.Data
namespace RamanujanPV.HighBudgetControlOO
open QuotientDemandCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem gaps_checked : checkGaps gaps gapCount=true := by decide +kernel
#print axioms gaps_checked
end RamanujanPV.HighBudgetControlOO
