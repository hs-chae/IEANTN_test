/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Interval.Source

namespace E1FrozenN.Interval
open Real Set MeasureTheory Complex
set_option maxHeartbeats 0

theorem zeroIncrement_derivative {x : ℝ} {rho : ℂ}
    (hx : 0 < x) (hrho : rho ≠ 0) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ rho / rho) ((x : ℂ) ^ (rho - 1)) x := by
  have hd := hasDerivAt_ofReal_cpow_const' (r := rho - 1) hx.ne'
    (by intro h; apply hrho; linear_combination h)
  simpa only [sub_add_cancel] using hd

/-- The derivative bound retains the interval length h. -/
theorem norm_zeroIncrement_le_derivative {x h : ℝ} {rho : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h) (him : 0 < rho.im) (hre : rho.re ≤ 1) :
    ‖zeroIncrement x h rho‖ ≤ h * x ^ (rho.re - 1) := by
  have hrho : rho ≠ 0 := by intro he; simp [he] at him
  have hrho1 : rho - 1 ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [sub_im, one_im, sub_zero, zero_im] at hi
    linarith
  have hd : ∀ t ∈ uIcc x (x+h),
      HasDerivAt (fun t : ℝ => (t : ℂ)^rho/rho) ((t : ℂ)^(rho-1)) t := by
    intro t ht
    rw [uIcc_of_le (by linarith : x ≤ x+h)] at ht
    exact zeroIncrement_derivative (hx.trans_le ht.1) hrho
  have hi : IntervalIntegrable (fun t : ℝ => (t : ℂ)^(rho-1)) volume x (x+h) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    intro t ht
    exact (hasDerivAt_ofReal_cpow_const (hx.trans_le ht.1).ne' hrho1).continuousAt.continuousWithinAt
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have hn : ‖∫ t in x..(x+h), (t : ℂ)^(rho-1)‖ ≤
      x^(rho.re-1) * |(x+h)-x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [uIoc_of_le (by linarith : x ≤ x+h)] at ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans_le ht.1.le)]
    simp only [sub_re, one_re]
    exact Real.rpow_le_rpow_of_nonpos hx ht.1.le (by linarith)
  rw [he] at hn
  simpa only [zeroIncrement, sub_div, add_sub_cancel_left, abs_of_nonneg hh, mul_comm] using hn

/-- The reciprocal-ordinate branch is useful above x/h. -/
theorem norm_zeroIncrement_le_reciprocal {x h : ℝ} {rho : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h) (him : 0 < rho.im) (hre : rho.re ≤ 1) :
    ‖zeroIncrement x h rho‖ ≤ x^rho.re * ((2+h/x)/rho.im) := by
  have hy : 0 < x+h := by linarith
  have hrho : 0 < ‖rho‖ := by
    apply lt_of_lt_of_le him
    exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
  have himn : rho.im ≤ ‖rho‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
  have hp : (x+h)^rho.re ≤ (x+h)*x^(rho.re-1) := by
    have hb := Real.rpow_le_rpow_of_nonpos hx (by linarith : x ≤ x+h)
      (by linarith : rho.re-1 ≤ 0)
    have he : (x+h)^rho.re = (x+h)*(x+h)^(rho.re-1) := by
      rw [Real.rpow_sub hy, Real.rpow_one]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hb hy.le
  have he : x^(rho.re-1)=x^rho.re/x := by rw [Real.rpow_sub hx, Real.rpow_one]
  calc
    ‖zeroIncrement x h rho‖ ≤ ((x+h)^rho.re+x^rho.re)/‖rho‖ := by
      unfold zeroIncrement
      rw [norm_div]
      apply div_le_div_of_nonneg_right _ hrho.le
      exact (norm_sub_le _ _).trans_eq (by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hy,
          Complex.norm_cpow_eq_rpow_re_of_pos hx])
    _ ≤ ((x+h)^rho.re+x^rho.re)/rho.im := by
      exact div_le_div_of_nonneg_left (by positivity) him himn
    _ ≤ ((x+h)*x^(rho.re-1)+x^rho.re)/rho.im := by gcongr
    _ = x^rho.re*((2+h/x)/rho.im) := by rw [he]; field_simp; ring

/-- The actual complex increment has the QRH-sensitive minimum height weight. -/
theorem norm_zeroIncrement_le_min {x h : ℝ} {rho : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h) (him : 0 < rho.im) (hre : rho.re ≤ 1) :
    ‖zeroIncrement x h rho‖ ≤
      x^rho.re * min (h/x) ((2+h/x)/rho.im) := by
  have ha := norm_zeroIncrement_le_derivative hx hh him hre
  have hb := norm_zeroIncrement_le_reciprocal hx hh him hre
  have he : h*x^(rho.re-1)=x^rho.re*(h/x) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    ring
  rw [he] at ha
  by_cases hmin : h/x ≤ (2+h/x)/rho.im
  · rw [min_eq_left hmin]
    exact ha
  · rw [min_eq_right (le_of_not_ge hmin)]
    exact hb

#print axioms norm_zeroIncrement_le_min
end E1FrozenN.Interval
