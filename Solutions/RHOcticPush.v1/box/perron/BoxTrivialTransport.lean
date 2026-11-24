import BoxTrivialSeries
import BoxIntegratedPopulation

/-! Exact transport of the full trivial-zero series. -/
namespace RHOcticPush.BoxPerron
open Real Set MeasureTheory
set_option maxHeartbeats 0

lemma trivial_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn IEANTN.RHSmoothing.trivial (Icc a b) := by
  intro x hx
  have hx1 : 1 < x := ha.trans_le hx.1
  have hx0 : x ≠ 0 := by linarith
  have harg : 1-x^(-2 : ℤ) ≠ 0 := by linarith [inverse_square_lt_one hx1]
  have hlog := Real.continuousAt_log harg
  have hp : ContinuousAt (fun t : ℝ => t^(-2 : ℤ)) x :=
    continuousAt_id.zpow₀ (-2) (Or.inl hx0)
  have hi : ContinuousAt (fun t : ℝ => 1-t^(-2 : ℤ)) x := continuousAt_const.sub hp
  exact ((hlog.comp (f := fun t : ℝ => 1-t^(-2 : ℤ)) hi).neg.div_const 2).continuousWithinAt

/-- Full convergent trivial-zero series, with the exact original logarithmic
trivial correction and its sign; no omitted endpoint or tail term. -/
theorem trivial_transport {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    transport a b (fun x => ((∑' n : ℕ, trivialPrimitive n x) : ℝ)) =
      -(∫ x in a..b, (IEANTN.RHSmoothing.trivial x : ℂ)/(x : ℂ)) := by
  have hc : ContinuousOn (fun x => ((-IEANTN.RHSmoothing.trivial x : ℝ) : ℂ))
      (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact Complex.continuous_ofReal.comp_continuousOn (trivial_continuousOn ha).neg
  rw [transport_of_hasDerivAt (by linarith : 0 < a) hab
    (fun x hx => (trivialTSum_hasDerivAt (ha.trans_le (by
      simpa only [min_eq_left hab] using hx.1))).ofReal_comp) hc.intervalIntegrable]
  simp only [Complex.ofReal_neg, neg_div, intervalIntegral.integral_neg]

#print axioms trivial_transport
end RHOcticPush.BoxPerron
