import RamanujanPV.HighBudgetControlOO.Final
open RamanujanPV.QuotientDemandCheck
example : checkGaps RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount = true := RamanujanPV.HighBudgetControlOO.gaps_checked
#print axioms RamanujanPV.HighBudgetControlOO.gaps_checked
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 0 16 = true := RamanujanPV.HighBudgetControlOO.part_0000
#print axioms RamanujanPV.HighBudgetControlOO.part_0000
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 16 16 = true := RamanujanPV.HighBudgetControlOO.part_0001
#print axioms RamanujanPV.HighBudgetControlOO.part_0001
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 32 16 = true := RamanujanPV.HighBudgetControlOO.part_0002
#print axioms RamanujanPV.HighBudgetControlOO.part_0002
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 48 16 = true := RamanujanPV.HighBudgetControlOO.part_0003
#print axioms RamanujanPV.HighBudgetControlOO.part_0003
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 64 16 = true := RamanujanPV.HighBudgetControlOO.part_0004
#print axioms RamanujanPV.HighBudgetControlOO.part_0004
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 80 16 = true := RamanujanPV.HighBudgetControlOO.part_0005
#print axioms RamanujanPV.HighBudgetControlOO.part_0005
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 96 16 = true := RamanujanPV.HighBudgetControlOO.part_0006
#print axioms RamanujanPV.HighBudgetControlOO.part_0006
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 112 16 = true := RamanujanPV.HighBudgetControlOO.part_0007
#print axioms RamanujanPV.HighBudgetControlOO.part_0007
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 128 16 = true := RamanujanPV.HighBudgetControlOO.part_0008
#print axioms RamanujanPV.HighBudgetControlOO.part_0008
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 144 16 = true := RamanujanPV.HighBudgetControlOO.part_0009
#print axioms RamanujanPV.HighBudgetControlOO.part_0009
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 160 16 = true := RamanujanPV.HighBudgetControlOO.part_0010
#print axioms RamanujanPV.HighBudgetControlOO.part_0010
example : allFrom (checkEntry RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount) 176 14 = true := RamanujanPV.HighBudgetControlOO.part_0011
#print axioms RamanujanPV.HighBudgetControlOO.part_0011
example : checkEntries RamanujanPV.HighBudgetControlOO.nodes RamanujanPV.HighBudgetControlOO.gaps RamanujanPV.HighBudgetControlOO.gapCount 190 = true := RamanujanPV.HighBudgetControlOO.entries_checked
#print axioms RamanujanPV.HighBudgetControlOO.entries_checked
example : RamanujanPV.HighBudgetControlOO.nodes.get 162 = ⟨2,32,1000,168,161,0,0,0,0,0,0,0⟩ := RamanujanPV.HighBudgetControlOO.root_1000
#print axioms RamanujanPV.HighBudgetControlOO.root_1000
example : RamanujanPV.HighBudgetControlOO.nodes.get 189 = ⟨2,20,367,73,188,0,0,0,0,0,0,0⟩ := RamanujanPV.HighBudgetControlOO.root_367
#print axioms RamanujanPV.HighBudgetControlOO.root_367
example : _root_.Nat.primeCounting 1000 = 168 := RamanujanPV.HighBudgetControlOO.pi_1000
#print axioms RamanujanPV.HighBudgetControlOO.pi_1000
example : _root_.Nat.primeCounting 367 = 73 := RamanujanPV.HighBudgetControlOO.pi_367
#print axioms RamanujanPV.HighBudgetControlOO.pi_367
