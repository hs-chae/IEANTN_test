import BoxPrefactorTaylor

/-! Limit algebra for the actual prefactor, for independently supplied regular terms. -/
namespace RHOcticPush.BoxGamma
open Real Filter Set
open scoped Topology

/-- The only hypotheses are ordinary derivatives of the two regular terms.
The actual zeta and convergent-series applications must supply those proofs. -/
theorem prefactor_laurent_product {R H : ℝ → ℝ} {r h : ℝ}
    (hR : HasDerivAt R r 0) (hH : HasDerivAt H h 0) :
    Tendsto (fun s : ℝ =>
      (prefactor s * (1/s + R s + H s) - 1/s -
        (1 - Real.eulerMascheroniConstant - Real.log 2 + R 0 + H 0)) / s)
      (𝓝[>] 0)
      (𝓝 (((1 - Real.eulerMascheroniConstant - Real.log 2)^2 + 1 + Real.pi^2 / 12) / 2 +
        (1 - Real.eulerMascheroniConstant - Real.log 2) * (R 0 + H 0) + r + h)) := by
  have htR : Tendsto (fun s : ℝ => (R s - R 0)/s) (𝓝[>] 0) (𝓝 r) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hR.tendsto_slope_zero_right
  have htH : Tendsto (fun s : ℝ => (H s - H 0)/s) (𝓝[>] 0) (𝓝 h) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hH.tendsto_slope_zero_right
  have htP := prefactor_hasDerivAt.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have htP1 : Tendsto (fun s : ℝ => (prefactor s - 1)/s) (𝓝[>] 0)
      (𝓝 (1 - Real.eulerMascheroniConstant - Real.log 2)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm, prefactor_zero] using
      prefactor_hasDerivAt.tendsto_slope_zero_right
  have ht := (prefactor_second_coefficient.add (htP1.mul_const (R 0 + H 0))).add
    (htP.mul (htR.add htH))
  simp only [prefactor_zero, one_mul] at ht
  have he :
      ((1 - Real.eulerMascheroniConstant - Real.log 2)^2 + 1 + Real.pi^2 / 12) / 2 +
        (1 - Real.eulerMascheroniConstant - Real.log 2) * (R 0 + H 0) + (r + h) =
      ((1 - Real.eulerMascheroniConstant - Real.log 2)^2 + 1 + Real.pi^2 / 12) / 2 +
        (1 - Real.eulerMascheroniConstant - Real.log 2) * (R 0 + H 0) + r + h := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := ne_of_gt hs
  field_simp
  ring

#print axioms prefactor_laurent_product
end RHOcticPush.BoxGamma
