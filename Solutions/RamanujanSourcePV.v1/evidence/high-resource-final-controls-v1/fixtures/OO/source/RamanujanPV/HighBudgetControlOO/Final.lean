/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientDemandCheck
import RamanujanPV.HighBudgetControlOO.GapCheck
import RamanujanPV.HighBudgetControlOO.Check0000
import RamanujanPV.HighBudgetControlOO.Check0001
import RamanujanPV.HighBudgetControlOO.Check0002
import RamanujanPV.HighBudgetControlOO.Check0003
import RamanujanPV.HighBudgetControlOO.Check0004
import RamanujanPV.HighBudgetControlOO.Check0005
import RamanujanPV.HighBudgetControlOO.Check0006
import RamanujanPV.HighBudgetControlOO.Check0007
import RamanujanPV.HighBudgetControlOO.Check0008
import RamanujanPV.HighBudgetControlOO.Check0009
import RamanujanPV.HighBudgetControlOO.Check0010
import RamanujanPV.HighBudgetControlOO.Check0011
namespace RamanujanPV.HighBudgetControlOO
open QuotientDemandCheck
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem union_0000 : allFrom (checkEntry nodes gaps gapCount) 0 16=true := part_0000
theorem union_0001 : allFrom (checkEntry nodes gaps gapCount) 0 32=true := allFrom_append_checked (i:=0) (n:=16) (m:=16) union_0000 part_0001
theorem union_0002 : allFrom (checkEntry nodes gaps gapCount) 0 48=true := allFrom_append_checked (i:=0) (n:=32) (m:=16) union_0001 part_0002
theorem union_0003 : allFrom (checkEntry nodes gaps gapCount) 0 64=true := allFrom_append_checked (i:=0) (n:=48) (m:=16) union_0002 part_0003
theorem union_0004 : allFrom (checkEntry nodes gaps gapCount) 0 80=true := allFrom_append_checked (i:=0) (n:=64) (m:=16) union_0003 part_0004
theorem union_0005 : allFrom (checkEntry nodes gaps gapCount) 0 96=true := allFrom_append_checked (i:=0) (n:=80) (m:=16) union_0004 part_0005
theorem union_0006 : allFrom (checkEntry nodes gaps gapCount) 0 112=true := allFrom_append_checked (i:=0) (n:=96) (m:=16) union_0005 part_0006
theorem union_0007 : allFrom (checkEntry nodes gaps gapCount) 0 128=true := allFrom_append_checked (i:=0) (n:=112) (m:=16) union_0006 part_0007
theorem union_0008 : allFrom (checkEntry nodes gaps gapCount) 0 144=true := allFrom_append_checked (i:=0) (n:=128) (m:=16) union_0007 part_0008
theorem union_0009 : allFrom (checkEntry nodes gaps gapCount) 0 160=true := allFrom_append_checked (i:=0) (n:=144) (m:=16) union_0008 part_0009
theorem union_0010 : allFrom (checkEntry nodes gaps gapCount) 0 176=true := allFrom_append_checked (i:=0) (n:=160) (m:=16) union_0009 part_0010
theorem union_0011 : allFrom (checkEntry nodes gaps gapCount) 0 190=true := allFrom_append_checked (i:=0) (n:=176) (m:=14) union_0010 part_0011
theorem entries_checked : checkEntries nodes gaps gapCount entryCount=true := union_0011
theorem root_1000 : nodes.get 162=⟨2,32,1000,168,161,0,0,0,0,0,0,0⟩ := by decide +kernel
theorem pi_1000 : Nat.primeCounting 1000=168 := by
  have h:=certificate_pi (i:=162) gaps_checked entries_checked (by decide) (by simpa only [root_1000] using (show (2:Nat)=2 by decide))
  simpa only [root_1000] using h
#print axioms pi_1000
theorem root_367 : nodes.get 189=⟨2,20,367,73,188,0,0,0,0,0,0,0⟩ := by decide +kernel
theorem pi_367 : Nat.primeCounting 367=73 := by
  have h:=certificate_pi (i:=189) gaps_checked entries_checked (by decide) (by simpa only [root_367] using (show (2:Nat)=2 by decide))
  simpa only [root_367] using h
#print axioms pi_367
end RamanujanPV.HighBudgetControlOO
