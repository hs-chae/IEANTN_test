/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.HighGroupedPilot.C0006
import RamanujanPV.HighGroupedPilot.C0000
import RamanujanPV.HighGroupedPilot.C2500
import RamanujanPV.HighGroupedPilot.C0047
namespace RamanujanPV.HighGroupedPilot.Independent
open QuotientDemandCheck HighTransitionCount
example : allFrom (checkEntry nodes gaps gapCount) 196608 32768=true := RamanujanPV.HighGroupedPilot.C0006.part_grouped
#print axioms RamanujanPV.HighGroupedPilot.C0006.part_grouped
example : allFrom (checkEntry nodes gaps gapCount) 0 32768=true := RamanujanPV.HighGroupedPilot.C0000.part_grouped
#print axioms RamanujanPV.HighGroupedPilot.C0000.part_grouped
example : allFrom (checkEntry nodes gaps gapCount) 81920000 32768=true := RamanujanPV.HighGroupedPilot.C2500.part_grouped
#print axioms RamanujanPV.HighGroupedPilot.C2500.part_grouped
example : allFrom (checkEntry nodes gaps gapCount) 1540096 32768=true := RamanujanPV.HighGroupedPilot.C0047.part_grouped
#print axioms RamanujanPV.HighGroupedPilot.C0047.part_grouped
end RamanujanPV.HighGroupedPilot.Independent
