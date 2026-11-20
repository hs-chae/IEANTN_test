import RamanujanPV.HighBudgetControlNormal.Final
open RamanujanPV.QuotientDemandCheck
example : checkGaps RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount = true := RamanujanPV.HighBudgetControlNormal.gaps_checked
#print axioms RamanujanPV.HighBudgetControlNormal.gaps_checked
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 0 16 = true := RamanujanPV.HighBudgetControlNormal.part_0000
#print axioms RamanujanPV.HighBudgetControlNormal.part_0000
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 16 16 = true := RamanujanPV.HighBudgetControlNormal.part_0001
#print axioms RamanujanPV.HighBudgetControlNormal.part_0001
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 32 16 = true := RamanujanPV.HighBudgetControlNormal.part_0002
#print axioms RamanujanPV.HighBudgetControlNormal.part_0002
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 48 16 = true := RamanujanPV.HighBudgetControlNormal.part_0003
#print axioms RamanujanPV.HighBudgetControlNormal.part_0003
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 64 16 = true := RamanujanPV.HighBudgetControlNormal.part_0004
#print axioms RamanujanPV.HighBudgetControlNormal.part_0004
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 80 16 = true := RamanujanPV.HighBudgetControlNormal.part_0005
#print axioms RamanujanPV.HighBudgetControlNormal.part_0005
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 96 16 = true := RamanujanPV.HighBudgetControlNormal.part_0006
#print axioms RamanujanPV.HighBudgetControlNormal.part_0006
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 112 16 = true := RamanujanPV.HighBudgetControlNormal.part_0007
#print axioms RamanujanPV.HighBudgetControlNormal.part_0007
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 128 16 = true := RamanujanPV.HighBudgetControlNormal.part_0008
#print axioms RamanujanPV.HighBudgetControlNormal.part_0008
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 144 16 = true := RamanujanPV.HighBudgetControlNormal.part_0009
#print axioms RamanujanPV.HighBudgetControlNormal.part_0009
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 160 16 = true := RamanujanPV.HighBudgetControlNormal.part_0010
#print axioms RamanujanPV.HighBudgetControlNormal.part_0010
example : allFrom (checkEntry RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount) 176 14 = true := RamanujanPV.HighBudgetControlNormal.part_0011
#print axioms RamanujanPV.HighBudgetControlNormal.part_0011
example : checkEntries RamanujanPV.HighBudgetControlNormal.nodes RamanujanPV.HighBudgetControlNormal.gaps RamanujanPV.HighBudgetControlNormal.gapCount 190 = true := RamanujanPV.HighBudgetControlNormal.entries_checked
#print axioms RamanujanPV.HighBudgetControlNormal.entries_checked
example : RamanujanPV.HighBudgetControlNormal.nodes.get 162 = ⟨2,32,1000,168,161,0,0,0,0,0,0,0⟩ := RamanujanPV.HighBudgetControlNormal.root_1000
#print axioms RamanujanPV.HighBudgetControlNormal.root_1000
example : RamanujanPV.HighBudgetControlNormal.nodes.get 189 = ⟨2,20,367,73,188,0,0,0,0,0,0,0⟩ := RamanujanPV.HighBudgetControlNormal.root_367
#print axioms RamanujanPV.HighBudgetControlNormal.root_367
example : _root_.Nat.primeCounting 1000 = 168 := RamanujanPV.HighBudgetControlNormal.pi_1000
#print axioms RamanujanPV.HighBudgetControlNormal.pi_1000
example : _root_.Nat.primeCounting 367 = 73 := RamanujanPV.HighBudgetControlNormal.pi_367
#print axioms RamanujanPV.HighBudgetControlNormal.pi_367
