import Mathlib
import PsiSmoothing
import IEANTN.Nodes.BoxMellinInputs.v1.Conclusions

namespace RHOcticPush.Box
open Real MeasureTheory Set
set_option maxHeartbeats 0

noncomputable def raw (j : ℕ) (y : ℝ) : ℝ :=
  (|Real.sin y / y| - if y ≤ 1 then 1 else 0) * Real.log y ^ j / y

lemma actual_eq_raw (j : ℕ) {y : ℝ} (hy : 0 < y) :
    BoxMellinInputs.v1.integrand j y = raw j y := by
  have he : IEANTN.RHSmoothing.fourier IEANTN.RHSmoothing.box y =
      Real.sin y / y := PsiSmoothing.box_fourier hy.ne'
  simp only [BoxMellinInputs.v1.integrand, raw, he]

lemma raw_measurable (j : ℕ) : Measurable (raw j) := by
  unfold raw
  have hi : Measurable (fun y : ℝ => if y ≤ 1 then (1 : ℝ) else 0) :=
    measurable_const.ite measurableSet_Iic measurable_const
  exact (((Real.continuous_sin.measurable.div measurable_id).abs.sub hi).mul
    (Real.measurable_log.pow_const j)).div measurable_id

lemma sinc_defect {y : ℝ} (hy : 0 < y) :
    abs (abs (Real.sin y / y) - 1) ≤ y ^ 2 / 6 := by
  have hs := Real.abs_sub_sin_le y
  rw [abs_of_pos hy] at hs
  calc
    abs (abs (Real.sin y / y) - 1) ≤ |Real.sin y / y - 1| := by
      simpa using abs_abs_sub_abs_le_abs_sub (Real.sin y / y) 1
    _ = |Real.sin y - y| / y := by
      rw [← div_self hy.ne', ← sub_div, abs_div, abs_of_pos hy]
    _ ≤ (y ^ 3 / 6) / y := by
      rw [abs_sub_comm] at hs
      exact div_le_div_of_nonneg_right hs hy.le
    _ = y ^ 2 / 6 := by field_simp <;> ring

lemma mul_log_small {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    y * |Real.log y| ≤ 1 := by
  have hlog : Real.log y ≤ 0 := Real.log_nonpos hy.le hy1
  rw [abs_of_nonpos hlog]
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at hi
  have h := mul_le_mul_of_nonneg_left hi hy.le
  have he : y * (y⁻¹ - 1) = 1-y := by field_simp <;> ring
  rw [he] at h
  linarith

lemma raw_small {j : ℕ} (hj : j ≤ 1) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖raw j y‖ ≤ 1 := by
  have hbase := sinc_defect hy
  have hl := mul_log_small hy hy1
  have he : ‖raw j y‖ = abs (abs (Real.sin y / y) - 1) * |Real.log y| ^ j / y := by
    simp [raw, if_pos hy1, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_pos hy]
  rw [he]
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbase (pow_nonneg (abs_nonneg (Real.log y)) j)) hy.le
  rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
  · norm_num only [pow_zero, mul_one] at hh ⊢
    have hd : (y ^ 2 / 6) / y = y / 6 := by field_simp <;> ring
    rw [hd] at hh
    linarith
  · norm_num only [pow_one] at hh ⊢
    have hd : (y ^ 2 / 6 * |Real.log y|) / y = y * |Real.log y| / 6 := by
      field_simp <;> ring
    rw [hd] at hh
    linarith

lemma raw_large {j : ℕ} (hj : j ≤ 1) {y : ℝ} (hy1 : 1 < y) :
    ‖raw j y‖ ≤ 2 * y ^ (-3 / 2 : ℝ) := by
  have hy : 0 < y := by linarith
  have hr : 1 ≤ y ^ (1 / 2 : ℝ) := Real.one_le_rpow hy1.le (by norm_num)
  have hl : |Real.log y| ^ j ≤ 2 * y ^ (1 / 2 : ℝ) := by
    rw [abs_of_nonneg (Real.log_nonneg hy1.le)]
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · norm_num only [pow_zero]; linarith
    · simp only [pow_one]
      have h := Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1/2 by norm_num)
      linarith
  have hb : |Real.sin y / y| ≤ 1 / y := by
    rw [abs_div, abs_of_pos hy]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one y) hy.le
  have he : ‖raw j y‖ = |Real.sin y / y| * |Real.log y| ^ j / y := by
    simp [raw, if_neg hy1.not_ge, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_pos hy]
  rw [he]
  have hm := mul_le_mul hb hl (pow_nonneg (abs_nonneg (Real.log y)) j)
    (by positivity : 0 ≤ 1 / y)
  have hh := div_le_div_of_nonneg_right hm hy.le
  have hpow : 2 * y ^ (-3 / 2 : ℝ) =
      ((1 / y) * (2 * y ^ (1 / 2 : ℝ))) / y := by
    rw [show (-3 / 2 : ℝ) = (1/2:ℝ)-2 by norm_num,
      Real.rpow_sub hy]
    norm_num only [Real.rpow_ofNat]
    field_simp <;> ring
  rw [hpow]
  exact hh

lemma raw_integrable_small {j : ℕ} (hj : j ≤ 1) :
    IntegrableOn (raw j) (Ioc (0:ℝ) 1) := by
  apply (integrableOn_const (C := (1:ℝ)) (s := Ioc (0:ℝ) 1) (by simp)).mono'
    (raw_measurable j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact raw_small hj hy.1 hy.2

lemma raw_integrable_large {j : ℕ} (hj : j ≤ 1) :
    IntegrableOn (raw j) (Ioi (1:ℝ)) := by
  apply ((integrableOn_Ioi_rpow_of_lt (show (-3/2:ℝ) < -1 by norm_num)
    (show (0:ℝ)<1 by norm_num)).const_mul 2).mono'
      (raw_measurable j).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  exact raw_large hj hy

/-- Both actual regularized absolute box moments are unconditionally integrable. -/
theorem actual_integrable {j : ℕ} (hj : j ≤ 1) :
    IntegrableOn (BoxMellinInputs.v1.integrand j) (Ioi (0:ℝ)) := by
  have hu : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := by ext x; simp <;> grind
  have hr : IntegrableOn (raw j) (Ioi (0:ℝ)) := by
    rw [← hu]
    exact (raw_integrable_small hj).union (raw_integrable_large hj)
  apply hr.congr_fun _ measurableSet_Ioi
  intro y hy
  exact (actual_eq_raw j hy).symm

/-- The integrability conjunct is not an additional analytic source assumption. -/
theorem first_moment_iff : BoxMellinInputs.v1.first_moment ↔
    IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 0 = Real.log 2 :=
  ⟨And.right, fun h => ⟨actual_integrable (by norm_num), h⟩⟩

/-- The remaining second-moment obligation is precisely the coefficient identity. -/
theorem second_moment_iff : BoxMellinInputs.v1.second_moment_identity ↔
    IEANTN.RHSmoothing.J IEANTN.RHSmoothing.box 1 =
      -BoxMellinInputs.v1.gamma1 - BoxMellinInputs.v1.q +
      BoxMellinInputs.v1.a * Real.log 2 - BoxMellinInputs.v1.a ^ 2 / 2 +
      1 / 2 + Real.pi ^ 2 / 24 :=
  ⟨And.right, fun h => ⟨actual_integrable (by norm_num), h⟩⟩

#print axioms actual_integrable
#print axioms first_moment_iff
#print axioms second_moment_iff
end RHOcticPush.Box
