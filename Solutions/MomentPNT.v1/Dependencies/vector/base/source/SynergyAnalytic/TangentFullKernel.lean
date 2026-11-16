import SynergyAnalytic.TangentTotals
namespace SynergyAnalytic.BoxModel
open ScopedNumerical
set_option maxHeartbeats 0
set_option maxRecDepth 200000
/-- Full272-cell mathematical integer-box model execution. Expected words
come from actual C output but are verified here by ordinary kernel reduction.
This is not a proof of C source execution or of model Real soundness. -/
theorem full256_kernel_execution : sourceBasis 256 = some (⟨634426550135877581749946416972346335033,634426550135877581749946416972346387067⟩,
⟨216480793147425769578523839282288619201,216480793147425769578523839282288654642⟩,
⟨175455803376318914922671818722729996020,175455803376318914922671818722730165340⟩) := by decide
#print axioms full256_kernel_execution
end SynergyAnalytic.BoxModel
