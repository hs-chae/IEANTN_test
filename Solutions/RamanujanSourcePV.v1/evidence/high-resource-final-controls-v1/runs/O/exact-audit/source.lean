import RamanujanPV.HighBudgetControlO.Final
open RamanujanPV.QuotientDemandCheck
example : checkGaps RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount = true := RamanujanPV.HighBudgetControlO.gaps_checked
#print axioms RamanujanPV.HighBudgetControlO.gaps_checked
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 0 16 = true := RamanujanPV.HighBudgetControlO.part_0000
#print axioms RamanujanPV.HighBudgetControlO.part_0000
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 16 16 = true := RamanujanPV.HighBudgetControlO.part_0001
#print axioms RamanujanPV.HighBudgetControlO.part_0001
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 32 16 = true := RamanujanPV.HighBudgetControlO.part_0002
#print axioms RamanujanPV.HighBudgetControlO.part_0002
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 48 16 = true := RamanujanPV.HighBudgetControlO.part_0003
#print axioms RamanujanPV.HighBudgetControlO.part_0003
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 64 16 = true := RamanujanPV.HighBudgetControlO.part_0004
#print axioms RamanujanPV.HighBudgetControlO.part_0004
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 80 16 = true := RamanujanPV.HighBudgetControlO.part_0005
#print axioms RamanujanPV.HighBudgetControlO.part_0005
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 96 16 = true := RamanujanPV.HighBudgetControlO.part_0006
#print axioms RamanujanPV.HighBudgetControlO.part_0006
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 112 16 = true := RamanujanPV.HighBudgetControlO.part_0007
#print axioms RamanujanPV.HighBudgetControlO.part_0007
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 128 16 = true := RamanujanPV.HighBudgetControlO.part_0008
#print axioms RamanujanPV.HighBudgetControlO.part_0008
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 144 16 = true := RamanujanPV.HighBudgetControlO.part_0009
#print axioms RamanujanPV.HighBudgetControlO.part_0009
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 160 16 = true := RamanujanPV.HighBudgetControlO.part_0010
#print axioms RamanujanPV.HighBudgetControlO.part_0010
example : allFrom (checkEntry RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount) 176 14 = true := RamanujanPV.HighBudgetControlO.part_0011
#print axioms RamanujanPV.HighBudgetControlO.part_0011
example : checkEntries RamanujanPV.HighBudgetControlO.nodes RamanujanPV.HighBudgetControlO.gaps RamanujanPV.HighBudgetControlO.gapCount 190 = true := RamanujanPV.HighBudgetControlO.entries_checked
#print axioms RamanujanPV.HighBudgetControlO.entries_checked
example : RamanujanPV.HighBudgetControlO.nodes.get 162 = ⟨2,32,1000,168,161,0,0,0,0,0,0,0⟩ := RamanujanPV.HighBudgetControlO.root_1000
#print axioms RamanujanPV.HighBudgetControlO.root_1000
example : RamanujanPV.HighBudgetControlO.nodes.get 189 = ⟨2,20,367,73,188,0,0,0,0,0,0,0⟩ := RamanujanPV.HighBudgetControlO.root_367
#print axioms RamanujanPV.HighBudgetControlO.root_367
example : _root_.Nat.primeCounting 1000 = 168 := RamanujanPV.HighBudgetControlO.pi_1000
#print axioms RamanujanPV.HighBudgetControlO.pi_1000
example : _root_.Nat.primeCounting 367 = 73 := RamanujanPV.HighBudgetControlO.pi_367
#print axioms RamanujanPV.HighBudgetControlO.pi_367
