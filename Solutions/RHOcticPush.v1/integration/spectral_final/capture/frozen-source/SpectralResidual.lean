import SpectralWeightedTransport
import BoxTrivialTransport
import AnchorScalar

/-! Small actual nonzero terms for the signed spectral transfer; all integrals
are complete physical integrals and all scalar checks use the ordinary kernel. -/
namespace RHOcticPush.Spectral076
open Real Complex Set MeasureTheory
open RHOcticPush.BoxPerron RHContinuation.Ramanujan
set_option maxHeartbeats 0
set_option leancert.trust "kernel"

lemma logWeight_primitive {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => -(Real.log t)⁻¹) (gmWeight x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hd := ((Real.hasDerivAt_log hx0).inv hl).neg
  apply hd.congr_deriv
  unfold gmWeight
  field_simp

theorem logWeight_integral {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in a..b,gmWeight t) = 1/Real.log a-1/Real.log b := by
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :=
    logWeight_primitive (ha.trans_le (by simpa only [min_eq_left hab] using hx.1))
  have hc : ContinuousOn gmWeight (uIcc a b) := by
    intro x hx
    exact (gmWeight_derivative (ha.trans_le (by
      simpa only [min_eq_left hab] using hx.1))).continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  simpa only [one_div,neg_sub_neg] using hi

lemma logWeight_integral_bounds {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    0 ≤ (∫ t in a..b,gmWeight t) ∧
      (∫ t in a..b,gmWeight t) ≤ 1/Real.log a := by
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro t ht
    unfold gmWeight
    have hl := Real.log_pos (ha.trans_le ht.1)
    have ht0 : 0 < t := by linarith [ht.1]
    positivity
  · rw [logWeight_integral ha hab]
    have hb := Real.log_pos (ha.trans_le hab)
    linarith [one_div_nonneg.mpr hb.le]

lemma actual_trivial_bounds {x : ℝ} (hx : 3 ≤ x) :
    0 ≤ IEANTN.RHSmoothing.trivial x ∧ IEANTN.RHSmoothing.trivial x ≤ 1/10 := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hq0 : 0 ≤ x^(-2 : ℤ) := zpow_nonneg hx0.le _
  have hq : x^(-2 : ℤ) ≤ (1/9 : ℝ) := by
    simp only [zpow_neg,zpow_ofNat]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 9)
      (by nlinarith : (9 : ℝ) ≤ x^2)
  have harg : (8/9 : ℝ) ≤ 1-x^(-2 : ℤ) := by linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 8/9) harg
  have hneg := Real.log_nonpos (by linarith : 0 ≤ 1-x^(-2 : ℤ))
    (by linarith : 1-x^(-2 : ℤ) ≤ 1)
  have hs : -(Real.log (8/9 : ℝ))/2 ≤ (1/10 : ℝ) := by
    interval_decide 80 (trust := kernel) <;> ring
  unfold IEANTN.RHSmoothing.trivial
  constructor <;> linarith

theorem actual_trivial_integral_bound {b : ℝ} (hb : 3 ≤ b) :
    ‖∫ t in (3 : ℝ)..b,(IEANTN.RHSmoothing.trivial t : ℂ)*(gmWeight t : ℂ)‖ ≤ 1/10 := by
  have hw := logWeight_integral_bounds (by norm_num : (1 : ℝ) < 3) hb
  have hlog : (1 : ℝ) < Real.log 3 := by interval_decide 80 (trust := kernel)
  have hW : (∫ t in (3 : ℝ)..b,gmWeight t) ≤ 1 := by
    have hdiv : (1 : ℝ)/Real.log 3 ≤ 1 := (div_le_one (by linarith)).mpr hlog.le
    exact hw.2.trans hdiv
  calc
    _ ≤ ∫ t in (3 : ℝ)..b,
        ‖(IEANTN.RHSmoothing.trivial t : ℂ)*(gmWeight t : ℂ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hb
    _ ≤ ∫ t in (3 : ℝ)..b,(1/10 : ℝ)*gmWeight t := by
      apply intervalIntegral.integral_mono_on hb
      · apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hb]
        exact (Complex.continuous_ofReal.comp_continuousOn
          (trivial_continuousOn (by norm_num : (1 : ℝ) < 3))).mul
          (Complex.continuous_ofReal.comp_continuousOn (by
            intro t ht
            exact (gmWeight_derivative (by linarith [ht.1] : 1 < t)).continuousAt.continuousWithinAt))
          |>.norm
      · apply ContinuousOn.intervalIntegrable
        intro t ht
        have ht1 : 1 < t := by have := ht.1; rw [min_eq_left hb] at this; linarith
        exact continuousWithinAt_const.mul
          (gmWeight_derivative ht1).continuousAt.continuousWithinAt
      · intro t ht
        have hh := actual_trivial_bounds ht.1
        have ht0 : 0 < t := by linarith [ht.1]
        have hp : 0 ≤ gmWeight t := by unfold gmWeight; positivity
        rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
          abs_of_nonneg hh.1,abs_of_nonneg hp]
        exact mul_le_mul_of_nonneg_right hh.2 hp
    _ = (1/10 : ℝ)*(∫ t in (3 : ℝ)..b,gmWeight t) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by linarith

theorem actual_linear_integral_bound {b : ℝ} (hb : 3 ≤ b) :
    ‖(Real.log (2*Real.pi) : ℂ)*
      ((∫ t in (3 : ℝ)..b,gmWeight t) : ℝ)‖ ≤ 17/10 := by
  have hw := logWeight_integral_bounds (by norm_num : (1 : ℝ) < 3) hb
  have hc : 0 ≤ Real.log (2*Real.pi) :=
    (Real.log_pos (by nlinarith [Real.pi_gt_three] : 1 < 2*Real.pi)).le
  have hs : Real.log (2*Real.pi)/Real.log 3 ≤ (17/10 : ℝ) := by
    have hh : Real.log (44/7 : ℝ)/Real.log 3 ≤ (17/10 : ℝ) := by
      interval_decide 80 (trust := kernel) <;> ring
    have hl := Real.log_le_log (by nlinarith [Real.pi_gt_three] : 0 < 2*Real.pi)
      (show 2*Real.pi ≤ (44/7 : ℝ) by linarith [Real.pi_lt_d4])
    exact (div_le_div_of_nonneg_right hl (Real.log_pos (by norm_num : (1:ℝ)<3)).le).trans hh
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hc,abs_of_nonneg hw.1]
  calc
    _ ≤ Real.log (2*Real.pi)*(1/Real.log 3) :=
      mul_le_mul_of_nonneg_left hw.2 hc
    _ = Real.log (2*Real.pi)/Real.log 3 := by ring
    _ ≤ _ := hs

lemma zero_anchor_scalar :
    (47/1000 : ℝ)*(Real.sqrt 3/(Real.log 3)^2) ≤ (2/25 : ℝ) := by
  have hs : Real.sqrt (3 : ℝ) ≤ 2 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
  have hl : (109/100 : ℝ) ≤ Real.log 3 := by
    interval_decide 80 (trust := kernel)
  rw [←mul_div_assoc]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (Real.log 3)^2)).mpr
  nlinarith [sq_nonneg (Real.log 3-109/100)]

#print axioms logWeight_integral
#print axioms actual_trivial_integral_bound
#print axioms actual_linear_integral_bound
#print axioms zero_anchor_scalar
end RHOcticPush.Spectral076
