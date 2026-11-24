import SpectralSquare
import BoxUniformIntegration

/-! Actual signed logarithmic transport, keeping both boundary terms and
complex phases until after the exact second primitive is obtained. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHContinuation.Ramanujan
set_option maxHeartbeats 0

noncomputable def weightedTransport (a b : ℝ) (F : ℝ → ℂ) : ℂ :=
  F b*(gmWeight b : ℂ)-F a*(gmWeight a : ℂ)+
    ∫ t in a..b,F t*(gmKernel t : ℂ)

theorem weightedTransport_of_hasDerivAt {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    {F F' : ℝ → ℂ} (hF : ∀ x ∈ uIcc a b,HasDerivAt F (F' x) x)
    (hi : IntervalIntegrable F' volume a b) :
    weightedTransport a b F = ∫ t in a..b,F' t*(gmWeight t : ℂ) := by
  have hw (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun t => (gmWeight t : ℂ)) (-(gmKernel x : ℂ)) x := by
    have hx1 : 1 < x := ha.trans_le (by simpa only [min_eq_left hab] using hx.1)
    simpa only [Complex.ofReal_neg] using (gmWeight_derivative hx1).ofReal_comp
  have hc : ContinuousOn (fun t => (gmKernel t : ℂ)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact Complex.continuous_ofReal.comp_continuousOn (gmKernel_continuousOn ha)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hw x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hF x ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt)
    (fun x hx => (hw x ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt) hi
    hc.neg.intervalIntegrable
  have he : (∫ t in a..b,F t*(-(gmKernel t : ℂ))) =
      -(∫ t in a..b,F t*(gmKernel t : ℂ)) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [he] at h
  unfold weightedTransport
  linear_combination -h

lemma zeroDensity_continuousOn {a b : ℝ} (ha : 1 < a)
    (r : IEANTN.RHSmoothing.Zero) : ContinuousOn
      (fun x : ℝ => Complex.exp ((r : ℂ)*(Real.log x : ℂ))*
        (IEANTN.zetaOrder r : ℂ)/(r : ℂ)) (Icc a b) := by
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hl := Real.continuousAt_log hx0
  fun_prop

lemma squareRemainder_continuousOn {a b : ℝ} (ha : 1 < a)
    (r : IEANTN.RHSmoothing.Zero) :
    ContinuousOn (fun x => squareRemainder x r) (Icc a b) := by
  intro x hx
  have hx1 : 1 < x := ha.trans_le hx.1
  have hx0 : x ≠ 0 := by linarith
  have hl0 : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
  have hl := Real.continuousAt_log hx0
  have hd : (x : ℂ)*(Real.log x : ℂ)^3 ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hx0)
      (pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hl0))
  unfold squareRemainder squareWave
  have hlc := Complex.continuous_ofReal.continuousAt.comp hl
  have hn : ContinuousAt (fun t : ℝ =>
      Complex.exp ((r : ℂ)*(Real.log t : ℂ))*squareCoefficient r) x :=
    (Complex.continuous_exp.continuousAt.comp
    (continuousAt_const.mul hlc)).mul_const (squareCoefficient r)
  have hdc := Complex.continuous_ofReal.continuousAt.mul (hlc.pow 3)
  exact (hn.div hdc hd).continuousWithinAt

/-- The exact cancellation that the unsigned primitive majorant discards.
All terms concern the actual zero and actual logarithmic weight. -/
theorem weighted_zero_exact {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (r : IEANTN.RHSmoothing.Zero) :
    weightedTransport a b (fun x => zeroPrimitive x r) =
      squareBoundary b r-squareBoundary a r+
        2*(∫ t in a..b,squareRemainder t r) := by
  have hd : ContinuousOn (fun x : ℝ => Complex.exp ((r : ℂ)*(Real.log x : ℂ))*
      (IEANTN.zetaOrder r : ℂ)/(r : ℂ)) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact zeroDensity_continuousOn ha r
  have hw : ContinuousOn (fun x => (gmWeight x : ℂ)) (uIcc a b) := by
    intro x hx
    have hx1 : 1 < x := ha.trans_le (by simpa only [min_eq_left hab] using hx.1)
    exact (gmWeight_derivative hx1).ofReal_comp.continuousAt.continuousWithinAt
  have hr : ContinuousOn (fun x => squareRemainder x r) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact squareRemainder_continuousOn ha r
  rw [weightedTransport_of_hasDerivAt ha hab
    (fun x hx => zeroPrimitive_hasDerivAt
      (by have : 1 < x := ha.trans_le (by simpa only [min_eq_left hab] using hx.1); linarith) r)
    hd.intervalIntegrable]
  have hi2 : IntervalIntegrable (fun t => (2 : ℂ)*squareRemainder t r) volume a b :=
    (continuousOn_const.mul hr).intervalIntegrable
  have hi1 : IntervalIntegrable (fun t : ℝ =>
      Complex.exp ((r : ℂ)*(Real.log t : ℂ))*(IEANTN.zetaOrder r : ℂ)/(r : ℂ)*
        (gmWeight t : ℂ)) volume a b := (hd.mul hw).intervalIntegrable
  have hs := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (hx : x ∈ uIcc a b) => squareBoundary_hasDerivAt
      (ha.trans_le (by simpa only [min_eq_left hab] using hx.1)) r)
    ((hd.mul hw).intervalIntegrable.sub hi2)
  rw [intervalIntegral.integral_sub hi1
    hi2, intervalIntegral.integral_const_mul] at hs
  linear_combination hs

#print axioms weightedTransport_of_hasDerivAt
#print axioms weighted_zero_exact
end RHOcticPush.Spectral076
