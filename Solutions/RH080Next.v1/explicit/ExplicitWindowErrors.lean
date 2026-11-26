/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitDomain
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
noncomputable section
open Real
namespace RH080Next.Explicit

def poleScale (c t : ℝ) : ℝ :=
  halfLogWidth c t * exp (t/2+halfLogWidth c t/2)

private theorem log_one_add_lower_quadratic (z : ℝ) (hz : 0 ≤ z) :
    z-z^2/2 ≤ log (1+z) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hz)
  apply (le_div_iff₀ (by linarith : 0 < z+2)).mpr
  nlinarith [pow_nonneg hz 3]

private theorem linear_exp_quarter_le (q : ℝ) (hq : 0 ≤ q) :
    q*exp (q/4) ≤ exp q-1 := by
  have hs : q/2 ≤ sinh (q/2) := Real.self_le_sinh_iff.mpr (by positivity)
  have hm := mul_le_mul_of_nonneg_right hs (le_of_lt (exp_pos (q/2)))
  have he1 : exp (q/2)*exp (q/2) = exp q := by
    rw [← exp_add]
    congr 1
    ring
  have he2 : exp (-(q/2))*exp (q/2) = 1 := by
    rw [← exp_add]
    simp
  rw [Real.sinh_eq] at hm
  have hqhalf : q*exp (q/2) ≤ exp q-1 := by nlinarith
  apply le_trans _ hqhalf
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hq

theorem poleScale_upper (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) : poleScale c t ≤ c*t/2 := by
  have hz := intervalRatio_pos c t hc ht
  have hq : 0 ≤ log (1+intervalRatio c t) := (Real.log_pos (by linarith)).le
  have hmain := linear_exp_quarter_le _ hq
  rw [Real.exp_log (by linarith : 0 < 1+intervalRatio c t), add_sub_cancel_left] at hmain
  have h := mul_le_mul_of_nonneg_left hmain (le_of_lt (div_pos (exp_pos (t/2)) (by norm_num : (0:ℝ)<2)))
  unfold poleScale halfLogWidth
  have he1 : exp (t/2+log (1+intervalRatio c t)/2/2) =
      exp (t/2)*exp (log (1+intervalRatio c t)/4) := by
    rw [← exp_add]
    congr 1
    ring
  rw [he1]
  have he2 : exp (t/2)*intervalRatio c t/2 = c*t/2 := by
    unfold intervalRatio
    rw [show -t/2 = -(t/2) by ring, exp_neg]
    field_simp
  nlinarith

theorem poleScale_lower (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) : c*t/2-(1/1000000:ℝ) ≤ poleScale c t := by
  have hz := intervalRatio_pos c t hc ht
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  have hql := log_one_add_lower_quadratic _ hz.le
  have hdl : intervalRatio c t/2-(intervalRatio c t)^2/4 ≤ halfLogWidth c t := by
    unfold halfLogWidth
    linarith
  have hexp : 1 ≤ exp (halfLogWidth c t/2) := Real.one_le_exp_iff.mpr (by positivity)
  have hmain := mul_le_mul_of_nonneg_right hdl (le_of_lt (exp_pos (t/2)))
  have hdmain := mul_le_mul_of_nonneg_left hexp (le_of_lt (mul_pos hd (exp_pos (t/2))))
  have he0 : intervalRatio c t*exp (t/2) = c*t := by
    unfold intervalRatio
    rw [mul_assoc, ← exp_add, show -t/2+t/2 = 0 by ring, exp_zero, mul_one]
  have he1 : (intervalRatio c t)^2*exp (t/2) = c^2*t^2*exp (-t/2) := by
    calc
      (intervalRatio c t)^2*exp (t/2) = intervalRatio c t*(intervalRatio c t*exp (t/2)) := by ring
      _ = intervalRatio c t*(c*t) := by rw [he0]
      _ = c^2*t^2*exp (-t/2) := by unfold intervalRatio; ring
  have hp := polynomial_exp_decay t ht 2 (by norm_num) (by norm_num)
  have he := exp_neg_twenty_one_upper
  have hc2 : c^2 ≤ 1 := by nlinarith
  have hpow := mul_le_mul_of_nonneg_right hc2
    (mul_nonneg (sq_nonneg t) (le_of_lt (exp_pos (-t/2))))
  unfold poleScale
  rw [exp_add]
  nlinarith

/-- Explicit logarithmic truncation-height allowance on the full continuous
logarithmic domain; no sampling of t is used. -/
theorem log_inverse_halfLogWidth_upper (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) :
    log (1/halfLogWidth c t) ≤ t/2-log (c*t/2)+(1/1000000:ℝ) := by
  have hz := intervalRatio_pos c t hc ht
  have hzu := intervalRatio_upper c t hc hc1 ht
  have hd := (halfLogWidth_bounds c t hc hc1 ht).1
  have hz1 : 0 < 1+intervalRatio c t := by linarith
  have hq := Real.one_sub_inv_le_log_of_pos hz1
  have hfrac : intervalRatio c t/(1+intervalRatio c t) = 1-(1+intervalRatio c t)⁻¹ := by
    field_simp
    <;> ring
  have hdl : intervalRatio c t/(2*(1+intervalRatio c t)) ≤ halfLogWidth c t := by
    unfold halfLogWidth
    rw [← hfrac] at hq
    rw [mul_comm (2:ℝ) (1+intervalRatio c t), ← div_div]
    exact div_le_div_of_nonneg_right hq (by norm_num)
  have hC : 0 ≤ 2*(1+intervalRatio c t)/intervalRatio c t := by positivity
  have hmul := mul_le_mul_of_nonneg_left hdl hC
  have hprod : (2*(1+intervalRatio c t)/intervalRatio c t)*
      (intervalRatio c t/(2*(1+intervalRatio c t))) = 1 := by
    field_simp
  rw [hprod] at hmul
  have hinv : 1/halfLogWidth c t ≤ 2*(1+intervalRatio c t)/intervalRatio c t :=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have hlog := Real.log_le_log (by positivity : 0 < 1/halfLogWidth c t) hinv
  have hct : 0 < c*t := by positivity
  have hlogz : log (intervalRatio c t) = log (c*t)-t/2 := by
    unfold intervalRatio
    rw [Real.log_mul hct.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hlogrhs : log (2*(1+intervalRatio c t)/intervalRatio c t) =
      t/2-log (c*t/2)+log (1+intervalRatio c t) := by
    rw [Real.log_div (mul_ne_zero (by norm_num) hz1.ne') hz.ne',
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hz1.ne', hlogz,
      Real.log_div hct.ne' (by norm_num : (2:ℝ) ≠ 0)]
    ring
  rw [hlogrhs] at hlog
  have hqu := Real.log_le_sub_one_of_pos hz1
  linarith

end RH080Next.Explicit
