import SynergyAnalytic.TangentFullKernel
namespace SynergyAnalytic.BoxModel
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
/-- Exact checked output-word comparisons. Converting the model words into
true integral bounds still requires the separately proved RealBox pipeline. -/
theorem sourceBasis256_target_words : ∃v:ProofBox×ProofBox×ProofBox,
    sourceBasis 256=some v ∧
    v.1.hi*200 ≤ 373*scale p ∧
    v.2.1.hi*2000 ≤ 1273*scale p ∧
    v.2.2.hi*250 ≤ 129*scale p := by
  refine ⟨_,full256_kernel_execution,?_,?_,?_⟩ <;> norm_num [scale,p]
#print axioms sourceBasis256_target_words
end SynergyAnalytic.BoxModel
