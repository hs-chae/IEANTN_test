import OcticDecay
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation and all-real derivative bounds for the actual octic transform.
No numerical execution leaf or additional analytic source hypothesis is used. -/
namespace RHOcticPush.DerivativeBounds
open Real MeasureTheory Set Filter
set_option maxHeartbeats 0

lemma cosine_integral_derivative (p : ℝ → ℝ) (hp : Continuous p) (y : ℝ) :
    HasDerivAt (fun v : ℝ => ∫ u in (-1 : ℝ)..1, p u * cos (v * u))
      (∫ u in (-1 : ℝ)..1, -(p u * u) * sin (y * u)) y := by
  have hF (v : ℝ) : Continuous (fun u : ℝ => p u * cos (v * u)) := by fun_prop
  have hG (v : ℝ) : Continuous (fun u : ℝ => -(p u * u) * sin (v * u)) := by fun_prop
  have hB : Continuous (fun u : ℝ => |p u * u|) := by fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (-1 : ℝ) 1)) (s := univ)
    (F := fun v u : ℝ => p u * cos (v * u))
    (F' := fun v u : ℝ => -(p u * u) * sin (v * u))
    (bound := fun u : ℝ => |p u * u|) (x₀ := y)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun v => (hF v).aestronglyMeasurable)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((hF y).intervalIntegrable _ _))
    (hG y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u v _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (hB.intervalIntegrable _ _))
    (Filter.Eventually.of_forall fun u v _ => by
      apply (((Real.hasDerivAt_cos (v * u)).comp v
        ((hasDerivAt_id v).mul_const u)).const_mul (p u)).congr_deriv
      ring)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h.2

lemma sine_integral_derivative (p : ℝ → ℝ) (hp : Continuous p) (y : ℝ) :
    HasDerivAt (fun v : ℝ => ∫ u in (-1 : ℝ)..1, p u * sin (v * u))
      (∫ u in (-1 : ℝ)..1, p u * u * cos (y * u)) y := by
  have hF (v : ℝ) : Continuous (fun u : ℝ => p u * sin (v * u)) := by fun_prop
  have hG (v : ℝ) : Continuous (fun u : ℝ => p u * u * cos (v * u)) := by fun_prop
  have hB : Continuous (fun u : ℝ => |p u * u|) := by fun_prop
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc (-1 : ℝ) 1)) (s := univ)
    (F := fun v u : ℝ => p u * sin (v * u))
    (F' := fun v u : ℝ => p u * u * cos (v * u))
    (bound := fun u : ℝ => |p u * u|) (x₀ := y)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun v => (hF v).aestronglyMeasurable)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      ((hF y).intervalIntegrable _ _))
    (hG y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u v _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (hB.intervalIntegrable _ _))
    (Filter.Eventually.of_forall fun u v _ => by
      apply (((Real.hasDerivAt_sin (v * u)).comp v
        ((hasDerivAt_id v).mul_const u)).const_mul (p u)).congr_deriv
      ring)
  simpa only [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using h.2

noncomputable def first (y : ℝ) :=
  ∫ u in (-1 : ℝ)..1, -(EvenKernel.kernel 4 u * u) * sin (y * u)
noncomputable def second (y : ℝ) :=
  ∫ u in (-1 : ℝ)..1, -(EvenKernel.kernel 4 u * u ^ 2) * cos (y * u)

theorem transform_hasDerivAt (y : ℝ) : HasDerivAt (EvenKernel.transform 4) (first y) y :=
  cosine_integral_derivative _ (EvenKernel.kernel_continuous 4) y

theorem first_hasDerivAt (y : ℝ) : HasDerivAt first (second y) y := by
  apply (sine_integral_derivative (fun u : ℝ => -(EvenKernel.kernel 4 u * u))
    ((EvenKernel.kernel_continuous 4).mul continuous_id).neg y).congr_deriv
  apply intervalIntegral.integral_congr
  intro u _
  ring

lemma integral_even (f : ℝ → ℝ) (hf : Continuous f) (he : ∀ u, f (-u) = f u) :
    (∫ u in (-1 : ℝ)..1, f u) = 2 * ∫ u in (0 : ℝ)..1, f u := by
  have hn : (∫ u in (-1 : ℝ)..0, f u) = ∫ u in (0 : ℝ)..1, f u := by
    calc
      _ = ∫ u in (-1 : ℝ)..0, f (-u) := by
        apply intervalIntegral.integral_congr
        intro u _
        exact (he u).symm
      _ = ∫ u in (0 : ℝ)..1, f u := by
        simpa only [neg_zero, neg_neg] using
          (intervalIntegral.integral_comp_neg (f := f) (a := (-1 : ℝ)) (b := 0))
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1)
  rw [hn] at hs
  linarith

lemma kernel_first_abs_moment :
    (∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u * |u|) = 4 / 5 := by
  rw [integral_even (fun u : ℝ => EvenKernel.kernel 4 u * |u|)
    ((EvenKernel.kernel_continuous 4).mul continuous_abs) (by
    intro u
    have hp : (-u) ^ (8 : ℕ) = u ^ 8 := by ring
    simp only [EvenKernel.kernel, Nat.reduceMul, hp, abs_neg])]
  have he : (∫ u in (0 : ℝ)..1, EvenKernel.kernel 4 u * |u|) =
      ∫ u in (0 : ℝ)..1, u - u ^ 9 := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    rw [EvenKernel.kernel_eq_raw 4 (by constructor <;> linarith [hu'.1, hu'.2]),
      abs_of_nonneg hu'.1]
    ring
  have h1 : IntervalIntegrable (fun u : ℝ => u) volume 0 1 :=
    continuous_id.intervalIntegrable _ _
  have h9 : IntervalIntegrable (fun u : ℝ => u ^ 9) volume 0 1 :=
    (by fun_prop : Continuous (fun u : ℝ => u ^ 9)).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_sub h1 h9, integral_id, integral_pow]
  norm_num

theorem first_abs_le (y : ℝ) : |first y| ≤ 4 / 5 := by
  have hc : Continuous (fun u : ℝ => -(EvenKernel.kernel 4 u * u) * sin (y * u)) :=
    (((EvenKernel.kernel_continuous 4).mul continuous_id).neg).mul (by fun_prop)
  calc
    _ ≤ ∫ u in (-1 : ℝ)..1, |-(EvenKernel.kernel 4 u * u) * sin (y * u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u * |u| := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hc.abs.intervalIntegrable _ _)
        (((EvenKernel.kernel_continuous 4).mul continuous_abs).intervalIntegrable _ _)
      intro u _
      rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (EvenKernel.kernel_nonneg 4 u)]
      exact mul_le_of_le_one_right (mul_nonneg (EvenKernel.kernel_nonneg 4 u)
        (abs_nonneg u)) (abs_sin_le_one _)
    _ = 4 / 5 := kernel_first_abs_moment

lemma kernel_second_moment :
    (∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u * u ^ 2) = 16 / 33 := by
  have he : (∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u * u ^ 2) =
      ∫ u in (-1 : ℝ)..1, u ^ 2 - u ^ 10 := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [EvenKernel.kernel_eq_raw 4
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu)]
    ring
  have h2 : IntervalIntegrable (fun u : ℝ => u ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => u ^ 2)).intervalIntegrable _ _
  have h10 : IntervalIntegrable (fun u : ℝ => u ^ 10) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => u ^ 10)).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_sub h2 h10, integral_pow, integral_pow]
  norm_num

theorem second_abs_le (y : ℝ) : |second y| ≤ 16 / 33 := by
  have hc : Continuous (fun u : ℝ => -(EvenKernel.kernel 4 u * u ^ 2) * cos (y * u)) :=
    (((EvenKernel.kernel_continuous 4).mul (continuous_id.pow 2)).neg).mul (by fun_prop)
  calc
    _ ≤ ∫ u in (-1 : ℝ)..1, |-(EvenKernel.kernel 4 u * u ^ 2) * cos (y * u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u * u ^ 2 := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hc.abs.intervalIntegrable _ _)
        (((EvenKernel.kernel_continuous 4).mul (continuous_id.pow 2)).intervalIntegrable _ _)
      intro u _
      rw [abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (EvenKernel.kernel_nonneg 4 u)
        (sq_nonneg u))]
      exact mul_le_of_le_one_right (mul_nonneg (EvenKernel.kernel_nonneg 4 u)
        (sq_nonneg u)) (abs_cos_le_one _)
    _ = 16 / 33 := kernel_second_moment

theorem transform_second_derivative (y : ℝ) :
    HasDerivAt (deriv (EvenKernel.transform 4)) (second y) y := by
  have he : deriv (EvenKernel.transform 4) = first := by
    funext v
    exact (transform_hasDerivAt v).deriv
  rw [he]
  exact first_hasDerivAt y

theorem transform_second_derivative_abs_le (y : ℝ) :
    |deriv (deriv (EvenKernel.transform 4)) y| ≤ 16 / 33 := by
  rw [(transform_second_derivative y).deriv]
  exact second_abs_le y

noncomputable def firstPrimitive (y u : ℝ) :=
  (u - u ^ 9) * cos (y * u) / y - (1 - 9 * u ^ 8) * sin (y * u) / y ^ 2

lemma firstPrimitive_derivative {y : ℝ} (hy : y ≠ 0) (u : ℝ) :
    HasDerivAt (firstPrimitive y)
      (-(u - u ^ 9) * sin (y * u) + 72 * (u ^ 7 * sin (y * u)) / y ^ 2) u := by
  have hi := hasDerivAt_id u
  have hs := (Real.hasDerivAt_sin (y * u)).comp u (hi.const_mul y)
  have hc := (Real.hasDerivAt_cos (y * u)).comp u (hi.const_mul y)
  have h0 := ((hi.sub (hi.pow 9)).mul hc).div_const y
  have h1 := (((hasDerivAt_const u (1 : ℝ)).sub ((hi.pow 8).const_mul 9)).mul hs).div_const (y ^ 2)
  apply (h0.sub h1).congr_deriv
  dsimp
  field_simp [hy]
  ring

theorem first_two_ibp {y : ℝ} (hy : y ≠ 0) :
    y ^ 2 * first y = 16 * sin y -
      72 * ∫ u in (-1 : ℝ)..1, u ^ 7 * sin (y * u) := by
  have he : first y = ∫ u in (-1 : ℝ)..1, -(u - u ^ 9) * sin (y * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    rw [EvenKernel.kernel_eq_raw 4
      (by simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu)]
    ring
  have h0 : IntervalIntegrable (fun u : ℝ => -(u - u ^ 9) * sin (y * u)) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => -(u - u ^ 9) * sin (y * u))).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun u : ℝ => 72 * (u ^ 7 * sin (y * u)) / y ^ 2) volume (-1) 1 :=
    (by fun_prop : Continuous (fun u : ℝ => 72 * (u ^ 7 * sin (y * u)) / y ^ 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun u _ => firstPrimitive_derivative hy u) (h0.add h1)
  rw [intervalIntegral.integral_add h0 h1, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, ← he] at h
  simp [firstPrimitive] at h
  field_simp [hy] at h
  simp only [mul_comm] at h ⊢
  nlinarith [h]

lemma seventh_abs_moment : (∫ u in (-1 : ℝ)..1, |u ^ 7|) = 1 / 4 := by
  rw [integral_even (fun u : ℝ => |u ^ 7|) (by fun_prop) (by intro u; simp)]
  have he : (∫ u in (0 : ℝ)..1, |u ^ 7|) = ∫ u in (0 : ℝ)..1, u ^ 7 := by
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    exact abs_of_nonneg (pow_nonneg hu'.1 _)
  rw [he, integral_pow]
  norm_num

lemma seventh_sine_integral_abs (y : ℝ) :
    |∫ u in (-1 : ℝ)..1, u ^ 7 * sin (y * u)| ≤ 1 / 4 := by
  have hc : Continuous (fun u : ℝ => u ^ 7 * sin (y * u)) := by fun_prop
  calc
    _ ≤ ∫ u in (-1 : ℝ)..1, |u ^ 7 * sin (y * u)| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ u in (-1 : ℝ)..1, |u ^ 7| := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hc.abs.intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun u : ℝ => |u ^ 7|)).intervalIntegrable _ _)
      intro u _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)
    _ = 1 / 4 := seventh_abs_moment

theorem first_quadratic_decay (y : ℝ) : y ^ 2 * |first y| ≤ 34 := by
  by_cases hy : y = 0
  · simp [hy]
  have h := first_two_ibp hy
  have ha : |y ^ 2 * first y| ≤
      16 * |sin y| + 72 * |∫ u in (-1 : ℝ)..1, u ^ 7 * sin (y * u)| := by
    rw [h]
    simpa [abs_mul, sub_eq_add_neg] using abs_add_le (16 * sin y)
      (-(72 * ∫ u in (-1 : ℝ)..1, u ^ 7 * sin (y * u)))
  rw [abs_mul, abs_of_nonneg (sq_nonneg y)] at ha
  have hs := abs_sin_le_one y
  have hi := seventh_sine_integral_abs y
  linarith

theorem first_abs_le_decay {y : ℝ} (hy : y ≠ 0) : |first y| ≤ 34 / y ^ 2 :=
  (le_div_iff₀ (sq_pos_of_ne_zero hy)).mpr
    (by simpa [mul_comm] using first_quadratic_decay y)

#print axioms transform_hasDerivAt
#print axioms first_abs_le
#print axioms first_quadratic_decay
#print axioms second_abs_le
#print axioms transform_second_derivative_abs_le
end RHOcticPush.DerivativeBounds
