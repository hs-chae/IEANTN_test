import SynergyAnalytic.HeightBudgetFold
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem kernel_budget_chunk5 : (List.range 4).all (fun j=>genericBudgetCheck (sumBudget 32 (32*(j+20)) zero) (blockWords[j+20]?))=true := by decide +kernel
#print axioms kernel_budget_chunk5
end SynergyAnalytic.HeightPoint
