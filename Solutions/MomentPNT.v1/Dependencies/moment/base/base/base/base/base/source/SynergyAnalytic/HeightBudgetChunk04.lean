import SynergyAnalytic.HeightBudgetFold
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem kernel_budget_chunk4 : (List.range 4).all (fun j=>genericBudgetCheck (sumBudget 32 (32*(j+16)) zero) (blockWords[j+16]?))=true := by decide +kernel
#print axioms kernel_budget_chunk4
end SynergyAnalytic.HeightPoint
