/- Source-checked C prefix words coincide with the exact numerical model sum.
This is the arithmetic correspondence needed for the later emitted-total consumer. -/
import SourceMainBudgetV1.All
import SynergyHeightC.MainBudgetFoldGeneric
import SynergyHeightC.MainWeightCellAbstract
namespace SynergyHeightC.MainBudgetSourceSum
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem cell_value (i : Nat) (hi : i < 768) :
    ∃ value, MainWeightModel.cell i=some value ∧
      ProofBox.add (SourceMainBudgetV1.Data.total i) value=
        SourceMainBudgetV1.Data.total (i+1) := by
  obtain ⟨input,pair,left,right,model,execution,next⟩ := SourceMainBudgetV1.All.cells i hi
  have same : MainBudgetExecute.right i=input := by
    simp only [MainBudgetExecute.right,right,Option.getD_some]
  refine ⟨MainWeightModel.term (MainBudgetExecute.left i) (MainBudgetExecute.right i)
    pair.1 pair.2,?_,next⟩
  rw [same]
  exact MainWeightModel.cell_from_pair_data left right model

theorem prefix_value (n : Nat) (bound : n ≤ 768) :
    MainWeightModel.prefixSum n=some (SourceMainBudgetV1.Data.total n) :=
  (congrFun MainBudgetFoldGeneric.actual_sum_function_exact n).trans
    (MainBudgetFoldGeneric.sum_of_recurrence MainWeightModel.cell
      SourceMainBudgetV1.Data.total SourceMainBudgetV1.Data.total_zero cell_value n bound)

#print axioms cell_value
#print axioms prefix_value
end SynergyHeightC.MainBudgetSourceSum
