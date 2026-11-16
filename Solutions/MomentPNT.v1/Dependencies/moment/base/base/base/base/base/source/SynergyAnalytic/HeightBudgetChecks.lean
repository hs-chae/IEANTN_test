import SynergyAnalytic.HeightBudgetChunk00
import SynergyAnalytic.HeightBudgetChunk01
import SynergyAnalytic.HeightBudgetChunk02
import SynergyAnalytic.HeightBudgetChunk03
import SynergyAnalytic.HeightBudgetChunk04
import SynergyAnalytic.HeightBudgetChunk05
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem kernel_budget_blocks : (List.range 24).all (fun b=>genericBudgetCheck (sumBudget 32 (32*b) zero) (blockWords[b]?))=true := by
  apply List.all_eq_true.mpr
  intro b hb
  have hb24 : b<24 := List.mem_range.mp hb
  interval_cases b
  · exact (List.all_eq_true.mp kernel_budget_chunk0) 0 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk0) 1 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk0) 2 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk0) 3 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk1) 0 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk1) 1 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk1) 2 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk1) 3 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk2) 0 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk2) 1 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk2) 2 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk2) 3 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk3) 0 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk3) 1 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk3) 2 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk3) 3 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk4) 0 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk4) 1 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk4) 2 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk4) 3 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk5) 0 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk5) 1 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk5) 2 (by decide)
  · exact (List.all_eq_true.mp kernel_budget_chunk5) 3 (by decide)

theorem kernel_budget_word_total : (∑b∈Finset.range 24,blockWords[b]?.getD 0)*500000 ≤ 4217*scale p := by decide +kernel
#print axioms kernel_budget_blocks
#print axioms kernel_budget_word_total
end SynergyAnalytic.HeightPoint
