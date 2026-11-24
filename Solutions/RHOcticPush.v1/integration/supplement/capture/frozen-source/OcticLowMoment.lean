import OcticFiniteQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
namespace RHOcticPush.Moments
open Real Set MeasureTheory
set_option maxHeartbeats 0
lemma octic_mass_lower (y : ℝ) :
    16/9 - (8/33)*y^2 ≤ EvenKernel.transform 4 y := by
  have hk := EvenKernel.kernel_continuous 4
  have hq : Continuous (fun u : ℝ => EvenKernel.kernel 4 u * u^2) := by fun_prop
  have he : (∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u*(1-(y*u)^2/2)) =
      (∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u) -
      y^2/2 * ∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u*u^2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (hk.intervalIntegrable _ _) ((hq.const_mul (y^2/2)).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  have hb : (∫ u in (-1 : ℝ)..1, EvenKernel.kernel 4 u*(1-(y*u)^2/2)) ≤
      EvenKernel.transform 4 y := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((by fun_prop : Continuous (fun u : ℝ =>
        EvenKernel.kernel 4 u*(1-(y*u)^2/2))).intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun u : ℝ =>
        EvenKernel.kernel 4 u*cos (y*u))).intervalIntegrable _ _)
    intro u _
    exact mul_le_mul_of_nonneg_left one_sub_sq_div_two_le_cos
      (EvenKernel.kernel_nonneg 4 u)
  rw [he, EvenKernel.kernel_mass 4, DerivativeBounds.kernel_second_moment] at hb
  norm_num [EvenKernel.mass] at hb
  nlinarith

lemma log_square_small {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    -(y^2*log y) ≤ 1/4 := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at h
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg y)
  have he : y^2*(y⁻¹-1) = y-y^2 := by field_simp <;> ring
  rw [he] at hm
  nlinarith [sq_nonneg (y-1/2)]

lemma low_log_point {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    |EvenKernel.transform 4 y| *log y ≤ (16/9)*log y+2/33 := by
  have hl : log y ≤ 0 := log_nonpos hy.le hy1
  have h0 := mul_le_mul_of_nonpos_right (le_abs_self (EvenKernel.transform 4 y)) hl
  have h1 := mul_le_mul_of_nonpos_right (octic_mass_lower y) hl
  have h2 := log_square_small hy hy1
  nlinarith

lemma octic_low_log_integrable :
    IntervalIntegrable (fun y => |EvenKernel.transform 4 y| *log y) volume 0 1 := by
  have hl : IntervalIntegrable log volume 0 1 := intervalIntegral.intervalIntegrable_log'
  simpa only [mul_comm] using hl.mul_continuousOn transform_abs_continuous.continuousOn

theorem octic_low_log :
    (∫ y in (0 : ℝ)..1, |EvenKernel.transform 4 y| *log y) ≤ -170/99 := by
  have hl : IntervalIntegrable log volume 0 1 := intervalIntegral.intervalIntegrable_log'
  calc
    _ ≤ ∫ y in (0 : ℝ)..1, (16/9)*log y+2/33 := by
      apply intervalIntegral.integral_mono_on (by norm_num) octic_low_log_integrable
        ((hl.const_mul (16/9 : ℝ)).add intervalIntegrable_const)
      intro y hy
      by_cases hy0 : y = 0
      · norm_num [hy0]
      exact low_log_point (by rcases hy with ⟨h, _⟩; exact lt_of_le_of_ne h (Ne.symm hy0)) hy.2
    _ = _ := by
      rw [intervalIntegral.integral_add (hl.const_mul (16/9 : ℝ))
        intervalIntegrable_const, intervalIntegral.integral_const_mul,
        integral_log, intervalIntegral.integral_const]
      norm_num
#print axioms octic_low_log
end RHOcticPush.Moments
