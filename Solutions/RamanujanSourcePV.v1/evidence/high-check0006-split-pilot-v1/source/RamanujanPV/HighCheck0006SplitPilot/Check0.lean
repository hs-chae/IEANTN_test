/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.HighTransitionCount.Data
namespace RamanujanPV.HighCheck0006SplitPilot
open QuotientDemandCheck HighTransitionCount
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem chunk_0 : allFrom (checkEntry nodes gaps gapCount) 196608 4096=true := by
  decide +kernel
#print axioms chunk_0
end RamanujanPV.HighCheck0006SplitPilot
