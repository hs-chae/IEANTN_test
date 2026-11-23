import OcticFourier

/-! Exact global majorants for the actual octic Fourier transform.  These are
analytic inequalities, not numerical certificates or source-first PV. -/
namespace RHOcticPush.Decay
open Real MeasureTheory Set
set_option maxHeartbeats 0

theorem transform_abs_le_mass (n : ℕ) (y : ℝ) :
    |EvenKernel.transform n y| ≤ EvenKernel.mass n := by
  have hi : Continuous (fun u : ℝ => EvenKernel.kernel n u * Real.cos (y * u)) := by
    exact (EvenKernel.kernel_continuous n).mul (by fun_prop)
  calc
    |EvenKernel.transform n y| ≤
        ∫ u in (-1 : ℝ)..1, |EvenKernel.kernel n u * Real.cos (y * u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, EvenKernel.kernel n u := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hi.abs.intervalIntegrable _ _) ((EvenKernel.kernel_continuous n).intervalIntegrable _ _)
      intro u _
      rw [abs_mul, abs_of_nonneg (EvenKernel.kernel_nonneg n u)]
      exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (EvenKernel.kernel_nonneg n u)).trans_eq (mul_one _)
    _ = EvenKernel.mass n := EvenKernel.kernel_mass n

noncomputable def ibpPrimitive (y u : ℝ) : ℝ :=
  (1 - u ^ 8) * Real.sin (y * u) / y - 8 * u ^ 7 * Real.cos (y * u) / y ^ 2

lemma ibpPrimitive_derivative {y : ℝ} (hy : y ≠ 0) (u : ℝ) :
    HasDerivAt (ibpPrimitive y)
      ((1 - u ^ 8) * Real.cos (y * u) - 56 * (u ^ 6 * Real.cos (y * u)) / y ^ 2) u := by
  have hi := hasDerivAt_id u
  have hs := (Real.hasDerivAt_sin (y * u)).comp u (hi.const_mul y)
  have hc := (Real.hasDerivAt_cos (y * u)).comp u (hi.const_mul y)
  have h0 := (((hasDerivAt_const u (1 : ℝ)).sub (hi.pow 8)).mul hs).div_const y
  have h1 := ((((hi.pow 7).const_mul 8).mul hc)).div_const (y ^ 2)
  apply (h0.sub h1).congr_deriv
  dsimp
  field_simp [hy]
  ring

theorem transform_two_ibp {y : ℝ} (hy : y ≠ 0) :
    y ^ 2 * EvenKernel.transform 4 y = -16 * Real.cos y +
      56 * ∫ u in (-1 : ℝ)..1, u ^ 6 * Real.cos (y * u) := by
  have he : EvenKernel.transform 4 y =
      ∫ u in (-1 : ℝ)..1, (1 - u ^ 8) * Real.cos (y * u) := by
    unfold EvenKernel.transform
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [EvenKernel.kernel_eq_raw 4 (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu)]
  have h0 : IntervalIntegrable (fun u : ℝ => (1 - u ^ 8) * Real.cos (y * u)) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => (1 - u ^ 8) * Real.cos (y * u))).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun u : ℝ => 56 * (u ^ 6 * Real.cos (y * u)) / y ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => 56 * (u ^ 6 * Real.cos (y * u)) / y ^ 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun u _ => ibpPrimitive_derivative hy u) (h0.sub h1)
  rw [intervalIntegral.integral_sub h0 h1, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, ← he] at h
  simp [ibpPrimitive] at h
  field_simp [hy] at h
  simp only [mul_comm] at h ⊢
  nlinarith [h]

lemma sixth_cos_integral_abs (y : ℝ) :
    |∫ u in (-1 : ℝ)..1, u ^ 6 * Real.cos (y * u)| ≤ 2 / 7 := by
  have hi : Continuous (fun u : ℝ => u ^ 6 * Real.cos (y * u)) := by fun_prop
  calc
    _ ≤ ∫ u in (-1 : ℝ)..1, |u ^ 6 * Real.cos (y * u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, u ^ 6 := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hi.abs.intervalIntegrable _ _)
        ((continuous_id.pow 6).intervalIntegrable _ _)
      intro u _
      have hu : 0 ≤ u ^ 6 := by positivity
      rw [abs_mul, abs_of_nonneg hu]
      simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hu
    _ = 2 / 7 := by rw [integral_pow]; norm_num

/-- An all-real decay inequality, including zero without a totalized-division argument. -/
theorem transform_quadratic_decay (y : ℝ) :
    y ^ 2 * |EvenKernel.transform 4 y| ≤ 32 := by
  by_cases hy : y = 0
  · simp [hy]
  have h := transform_two_ibp hy
  have ha : |y ^ 2 * EvenKernel.transform 4 y| ≤
      16 * |Real.cos y| + 56 * |∫ u in (-1 : ℝ)..1, u ^ 6 * Real.cos (y * u)| := by
    rw [h]
    simpa [abs_mul] using abs_add_le (-16 * Real.cos y)
      (56 * ∫ u in (-1 : ℝ)..1, u ^ 6 * Real.cos (y * u))
  rw [abs_mul, abs_of_nonneg (sq_nonneg y)] at ha
  have hc := Real.abs_cos_le_one y
  have hi := sixth_cos_integral_abs y
  linarith

theorem transform_abs_le_decay {y : ℝ} (hy : y ≠ 0) :
    |EvenKernel.transform 4 y| ≤ 32 / y ^ 2 :=
  (le_div_iff₀ (sq_pos_of_ne_zero hy)).mpr (by simpa [mul_comm] using transform_quadratic_decay y)

/-- A positive reciprocal-square envelope with no small-ordinate exception. -/
theorem transform_weighted_majorant (y : ℝ) :
    (1 + y ^ 2) * |EvenKernel.transform 4 y| ≤ 304 / 9 := by
  have h0 := transform_abs_le_mass 4 y
  norm_num [EvenKernel.mass] at h0
  have h2 := transform_quadratic_decay y
  nlinarith

#print axioms transform_abs_le_mass
#print axioms transform_two_ibp
#print axioms transform_quadratic_decay
#print axioms transform_weighted_majorant
end RHOcticPush.Decay
