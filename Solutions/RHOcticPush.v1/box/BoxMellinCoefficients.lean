import BoxMellinNormalization

namespace RHOcticPush.BoxMellin
open Real Filter Set
open scoped Topology

/-- The actual first box moment is the right finite part of its absolute Mellin integral. -/
theorem finite_part_tendsto :
    Tendsto (fun s : ℝ => mellin s - 1/s) (𝓝[>] 0)
      (𝓝 (IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0)) := by
  have ht := regularized_hasDerivAt.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  rw [regularized_zero] at ht
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with s hs
  have he := mellin_renormalized hs.1 hs.2
  linarith

/-- The actual logarithmic box moment is the linear Laurent coefficient.
This proves coefficient extraction, not its evaluation through Gamma or zeta. -/
theorem linear_coefficient_tendsto :
    Tendsto (fun s : ℝ =>
      (mellin s - 1/s - IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0)/s)
      (𝓝[>] 0) (𝓝 (IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1)) := by
  have ht : Tendsto (fun s : ℝ =>
      (regularizedMellin s - IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0)/s)
      (𝓝[>] 0) (𝓝 (IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1)) := by
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm,regularized_zero] using
      regularized_hasDerivAt.tendsto_slope_zero_right
  apply ht.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with s hs
  have he := mellin_renormalized hs.1 hs.2
  congr 1
  linarith

#print axioms finite_part_tendsto
#print axioms linear_coefficient_tendsto
end RHOcticPush.BoxMellin
