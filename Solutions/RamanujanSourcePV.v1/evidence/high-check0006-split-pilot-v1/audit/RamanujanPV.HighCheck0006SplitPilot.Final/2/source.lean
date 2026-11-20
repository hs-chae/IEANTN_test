/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.HighCheck0006SplitPilot.Bridge
import RamanujanPV.HighCheck0006SplitPilot.Check0
import RamanujanPV.HighCheck0006SplitPilot.Check1
import RamanujanPV.HighCheck0006SplitPilot.Check2
import RamanujanPV.HighCheck0006SplitPilot.Check3
import RamanujanPV.HighCheck0006SplitPilot.Check4
import RamanujanPV.HighCheck0006SplitPilot.Check5
import RamanujanPV.HighCheck0006SplitPilot.Check6
import RamanujanPV.HighCheck0006SplitPilot.Check7
namespace RamanujanPV.HighCheck0006SplitPilot
open QuotientDemandCheck HighTransitionCount
set_option maxHeartbeats 0
theorem part_0006_split : allFrom (checkEntry nodes gaps gapCount) 196608 32768=true := by
  have tail6 : allFrom (checkEntry nodes gaps gapCount) 221184 8192=true := append_checked (n:=4096) (m:=4096) chunk_6 chunk_7
  have tail5 : allFrom (checkEntry nodes gaps gapCount) 217088 12288=true := append_checked (n:=4096) (m:=8192) chunk_5 tail6
  have tail4 : allFrom (checkEntry nodes gaps gapCount) 212992 16384=true := append_checked (n:=4096) (m:=12288) chunk_4 tail5
  have tail3 : allFrom (checkEntry nodes gaps gapCount) 208896 20480=true := append_checked (n:=4096) (m:=16384) chunk_3 tail4
  have tail2 : allFrom (checkEntry nodes gaps gapCount) 204800 24576=true := append_checked (n:=4096) (m:=20480) chunk_2 tail3
  have tail1 : allFrom (checkEntry nodes gaps gapCount) 200704 28672=true := append_checked (n:=4096) (m:=24576) chunk_1 tail2
  have tail0 : allFrom (checkEntry nodes gaps gapCount) 196608 32768=true := append_checked (n:=4096) (m:=28672) chunk_0 tail1
  exact tail0
example : allFrom (checkEntry nodes gaps gapCount) 196608 32768=true := part_0006_split
#print axioms part_0006_split
end RamanujanPV.HighCheck0006SplitPilot
