import CertifiedCrossing

/-! Native evaluation evidence. Unlike the above generic theorem, this file
depends on the compiled execution of the large finite prime-count queries. -/
namespace Crossing
set_option maxHeartbeats 0
set_option maxRecDepth 65536
theorem native_count_K : LocalPrimeSieve.count K = P := by native_decide
theorem native_count_Y : LocalPrimeSieve.count Y = Q := by native_decide
theorem native_root :
    ∃ r : ℝ, (lo:ℝ) < r ∧ r < (hi:ℝ) ∧ RHReal.Gap r = 0 ∧
      (∀ x ∈ Set.Ico (K:ℝ) ((K:ℝ)+1), x < r → RHReal.Gap x < 0) ∧
      (∀ x ∈ Set.Ico (K:ℝ) ((K:ℝ)+1), r < x → 0 < RHReal.Gap x) :=
  crossing native_count_K native_count_Y
#print axioms native_root
end Crossing
