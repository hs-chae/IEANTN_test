import FKS2SumBridge.Integration
import IEANTN.Nodes.FKS2Numerics.v2.Conclusions

namespace FKS2SumBridge

/-- The original source/stability proof discharges the corrected numerical-node premise. -/
theorem corrected_node_multiplier : FKS2Numerics.v2.nu_asymp_e30_le := by
  change FKS2Numerics.v1.nuAsympE30 ≤ IEANTN.margin 0 * (6.339e-7 : ℝ)
  have h := relaxed_upper_bound_via_stability
  norm_num [IEANTN.margin, FKS2Scalar.Bpoc] at h ⊢
  exact h

end FKS2SumBridge
