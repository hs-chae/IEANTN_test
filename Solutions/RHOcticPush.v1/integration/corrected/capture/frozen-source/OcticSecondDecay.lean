import OcticDerivativeBounds
namespace RHOcticPush.SecondDecay
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def primitive (y u : ℝ) :=
  (u^2-u^10)*sin (y*u)/y + (2*u-10*u^9)*cos (y*u)/y^2
lemma primitive_derivative {y : ℝ} (hy : y ≠ 0) (u : ℝ) :
    HasDerivAt (primitive y)
      ((u^2-u^10)*cos (y*u)+(2-90*u^8)*cos (y*u)/y^2) u := by
  have hi := hasDerivAt_id u
  have hs := (Real.hasDerivAt_sin (y*u)).comp u (hi.const_mul y)
  have hc := (Real.hasDerivAt_cos (y*u)).comp u (hi.const_mul y)
  have h0 := (((hi.pow 2).sub (hi.pow 10)).mul hs).div_const y
  have h1 := (((hi.const_mul 2).sub ((hi.pow 9).const_mul 10)).mul hc).div_const (y^2)
  apply (h0.add h1).congr_deriv
  dsimp
  field_simp [hy]
  ring
lemma second_ibp {y : ℝ} (hy : y ≠ 0) :
    y^2*DerivativeBounds.second y = 16*cos y +
      ∫ u in (-1 : ℝ)..1, (2-90*u^8)*cos (y*u) := by
  have he : DerivativeBounds.second y =
      -(∫ u in (-1 : ℝ)..1, (u^2-u^10)*cos (y*u)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp [DerivativeBounds.second]
    rw [EvenKernel.kernel_eq_raw 4
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu)]
    ring
  have h0 : IntervalIntegrable (fun u : ℝ => (u^2-u^10)*cos (y*u)) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => (u^2-u^10)*cos (y*u))).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun u : ℝ => (2-90*u^8)*cos (y*u)/y^2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => (2-90*u^8)*cos (y*u)/y^2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun u _ => primitive_derivative hy u) (h0.add h1)
  rw [intervalIntegral.integral_add h0 h1, intervalIntegral.integral_div] at h
  rw [he]
  simp [primitive] at h
  field_simp [hy] at h
  have hi : (∫ u in (-1 : ℝ)..1, u^2*(1-u^8)*cos (u*y)) =
      ∫ u in (-1 : ℝ)..1, (u^2-u^10)*cos (y*u) := by
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    rw [mul_comm u y]
    ring
  rw [hi] at h
  nlinarith [h]
lemma remainder_bound (y : ℝ) :
    |∫ u in (-1 : ℝ)..1, (2-90*u^8)*cos (y*u)| ≤ 24 := by
  have hc : Continuous (fun u : ℝ => (2-90*u^8)*cos (y*u)) := by fun_prop
  have hm : Continuous (fun u : ℝ => 2+90*u^8) := by fun_prop
  calc
    _ ≤ ∫ u in (-1 : ℝ)..1, |(2-90*u^8)*cos (y*u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, (2+90*u^8) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.abs.intervalIntegrable _ _) (hm.intervalIntegrable _ _)
      intro u _
      rw [abs_mul]
      calc
        _ ≤ |2-90*u^8| := mul_le_of_le_one_right (abs_nonneg _)
          (abs_cos_le_one _)
        _ ≤ 2+90*u^8 := by
          have hp : 0 ≤ u^8 := by positivity
          rw [abs_le]
          constructor <;> nlinarith
    _ = 24 := by
      rw [intervalIntegral.integral_add
        (continuous_const.intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun u : ℝ => 90*u^8)).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_pow]
      norm_num

theorem second_quadratic_decay (y : ℝ) : y^2*|DerivativeBounds.second y| ≤ 40 := by
  by_cases hy : y = 0
  · simp [hy]
  have h := second_ibp hy
  have ha : |y^2*DerivativeBounds.second y| ≤
      16*|cos y|+|∫ u in (-1 : ℝ)..1, (2-90*u^8)*cos (y*u)| := by
    rw [h]
    simpa [abs_mul] using abs_add_le (16*cos y)
      (∫ u in (-1 : ℝ)..1, (2-90*u^8)*cos (y*u))
  rw [abs_mul, abs_of_nonneg (sq_nonneg y)] at ha
  linarith [remainder_bound y, abs_cos_le_one y]
#print axioms second_quadratic_decay
end RHOcticPush.SecondDecay
