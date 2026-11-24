import BoxUniformIntegration

namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma zeroPrimitive_continuousOn {a b : ℝ} (ha : 1 < a)
    (ρ : IEANTN.RHSmoothing.Zero) : ContinuousOn (fun x => zeroPrimitive x ρ) (Icc a b) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) (ha.trans_le hx.1))
  have hlog : ContinuousAt Real.log x := Real.continuousAt_log hx0
  unfold zeroPrimitive
  fun_prop

lemma zeroIntegrand_continuousOn {a b : ℝ} (ha : 1 < a)
    (ρ : IEANTN.RHSmoothing.Zero) :
    ContinuousOn (fun x : ℝ => zeroPrimitive x ρ / (x : ℂ)^2) (Icc a b) := by
  apply (zeroPrimitive_continuousOn ha ρ).div
    ((Complex.continuous_ofReal.pow 2).continuousOn)
  intro x hx
  exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1) (ha.trans_le hx.1))))

lemma zeroIntegrand_uniform {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (x : ℝ) (hx : x ∈ Icc a b) (ρ : IEANTN.RHSmoothing.Zero) :
    ‖zeroPrimitive x ρ / (x : ℂ)^2‖ ≤
      Real.exp (2 * Real.log b) * ‖zeroCoefficient ρ‖ := by
  have hx1 : 1 ≤ x := ha.le.trans hx.1
  have hx0 : 0 ≤ x := by linarith
  calc
    ‖zeroPrimitive x ρ / (x : ℂ)^2‖ = ‖zeroPrimitive x ρ‖ / x^2 := by
      simp [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    _ ≤ ‖zeroPrimitive x ρ‖ := div_le_self (norm_nonneg _) (by nlinarith)
    _ ≤ _ := zeroPrimitive_uniform ha hab x hx ρ

/-- Interchange for the ACTUAL integrated all-zero family, without RH and
without assuming countability of all nontrivial zeta zeros. -/
theorem zero_integral_tsum {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    (∑' ρ, ∫ x in a..b, zeroPrimitive x ρ / (x : ℂ)^2) =
      ∫ x in a..b, (∑' ρ, zeroPrimitive x ρ) / (x : ℂ)^2 := by
  have ht := interval_tsum_uniform hab zeroCoefficient (zeroCoefficient_summable h)
    (fun ρ x => zeroPrimitive x ρ / (x : ℂ)^2)
    (zeroIntegrand_continuousOn ha) (fun ρ x hx => zeroIntegrand_uniform ha hab x hx ρ)
  simpa only [tsum_div_const] using ht

theorem zero_integral_summable {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    Summable (fun ρ => ∫ x in a..b, zeroPrimitive x ρ / (x : ℂ)^2) := by
  apply (((zeroCoefficient_summable h).norm.mul_left (Real.exp (2 * Real.log b))).mul_right
    |b-a|).of_norm_bounded
  intro ρ
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro x hx
  exact zeroIntegrand_uniform ha hab x
    (Ioc_subset_Icc_self (by simpa only [uIoc_of_le hab] using hx)) ρ

theorem zero_transport_summable {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    Summable (fun ρ => transport a b (fun x => zeroPrimitive x ρ)) := by
  exact ((zeroPrimitive_summable h ha hab (show b ∈ Icc a b from ⟨hab, le_rfl⟩)).div_const
    (b : ℂ) |>.sub
    ((zeroPrimitive_summable h ha hab (show a ∈ Icc a b from ⟨le_rfl, hab⟩)).div_const
      (a : ℂ))).add (zero_integral_summable h ha hab)

/-- Exact interchange with the COMPLETE transport operator, including both
boundary evaluations; this is the zero-sum step used in the averaged EF. -/
theorem zero_transport_tsum {a b : ℝ} (h : SourceIntegratedPsi)
    (ha : 1 < a) (hab : a ≤ b) :
    (∑' ρ, transport a b (fun x => zeroPrimitive x ρ)) =
      transport a b (fun x => ∑' ρ, zeroPrimitive x ρ) := by
  have hA := (zeroPrimitive_summable h ha hab (show a ∈ Icc a b from ⟨le_rfl, hab⟩)).div_const
    (a : ℂ)
  have hB := (zeroPrimitive_summable h ha hab (show b ∈ Icc a b from ⟨hab, le_rfl⟩)).div_const
    (b : ℂ)
  have hI := zero_integral_summable h ha hab
  unfold transport
  rw [(hB.sub hA).tsum_add hI, hB.tsum_sub hA, tsum_div_const, tsum_div_const,
    zero_integral_tsum h ha hab]

#print axioms zero_integral_tsum
#print axioms zero_integral_summable
#print axioms zero_transport_tsum
#print axioms zero_transport_summable
end RHOcticPush.BoxPerron
