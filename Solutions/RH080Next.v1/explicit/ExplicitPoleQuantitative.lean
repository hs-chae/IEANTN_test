/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitPoleError

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.Explicit

private theorem halfLogWidth_le_ratio (c t : ℝ) (hc : (1/2:ℝ) ≤ c)
    (ht : 42 ≤ t) : halfLogWidth c t ≤ intervalRatio c t/2 := by
  have hz := intervalRatio_pos c t hc ht
  have h := log_le_sub_one_of_pos (by linarith : 0 < 1+intervalRatio c t)
  unfold halfLogWidth
  linarith

/-- The radius-dependent quadratic pole loss is below the original allowance
on the entire continuous domain. This is substantially sharper than needed;
200 is a permissive finite bound for the nodal second-moment provider. -/
theorem pole_quadratic_loss_lt (c t mu : ℝ) (hc : (1/2:ℝ) ≤ c)
    (hc1 : c ≤ 1) (ht : 42 ≤ t) (hmu0 : 0 ≤ mu) (hmu : mu ≤ 200) :
    poleScale c t*(halfLogWidth c t/2)^2*mu < (1/10000000000:ℝ) := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hd0 := hd.1
  have hdl := halfLogWidth_le_ratio c t hc ht
  have hp := poleScale_upper c t hc hc1 ht
  have he := exp_neg_twenty_one_upper
  have ht0 : 0 ≤ t := by linarith
  have hz := intervalRatio_pos c t hc ht
  have hdcap : (halfLogWidth c t/2)^2 ≤ (intervalRatio c t)^2/16 := by
    nlinarith [sq_nonneg (intervalRatio c t/2-halfLogWidth c t)]
  have hc2 : c^2 ≤ 1 := by nlinarith
  have hzsq : (intervalRatio c t)^2 ≤ t^2*exp (-t) := by
    have heq : (intervalRatio c t)^2 = c^2*t^2*exp (-t) := by
      unfold intervalRatio
      rw [mul_pow,mul_pow,←exp_nat_mul]
      congr 2 <;> ring
    rw [heq]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (sq_nonneg t)) (exp_pos (-t)).le
  have hp0 : 0 ≤ poleScale c t := by unfold poleScale; positivity
  have hbound : poleScale c t*(halfLogWidth c t/2)^2*mu ≤
      200*t^3*exp (-t)/32 := by
    calc
      _ ≤ (t/2)*((t^2*exp (-t))/16)*200 := by
        apply mul_le_mul (mul_le_mul (hp.trans (by nlinarith))
          (hdcap.trans (div_le_div_of_nonneg_right hzsq (by norm_num)))
          (sq_nonneg _) (by positivity)) hmu hmu0 (by positivity)
      _ = _ := by ring
  have ht3 := polynomial_exp_decay t ht 3 (by norm_num) (by norm_num)
  have hemono : exp (-t/2) ≤ exp (-21) := exp_le_exp.mpr (by linarith)
  have hepos := (exp_pos (-21)).le
  have hm := mul_le_mul ht3 hemono (exp_pos _).le (by positivity : 0 ≤ (42:ℝ)^3*exp (-21))
  have heq : t^3*exp (-t/2)*exp (-t/2) = t^3*exp (-t) := by
    rw [mul_assoc,←exp_add]
    congr 1
    ring
  rw [heq] at hm
  have hs : exp (-21)^2 < (1/1050000000:ℝ)^2 :=
    pow_lt_pow_left₀ he (exp_pos _).le (by norm_num)
  nlinarith

theorem actual_mellin_pole_lower_domain (nodes : List ℚ) (m : ℕ)
    (hlen : 2 ≤ nodes.length) (hm : 0 < m)
    (hlast : node nodes (nodes.length-1) = 0) (hR : radius nodes m ≤ 10)
    (hmu0 : 0 ≤ nodalMu2Upper nodes m) (hmu : nodalMu2Upper nodes m ≤ 200)
    (c t : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t) :
    poleScale c t*nodalF0 nodes m-(1/10000000000:ℝ) <
      poleScale c t*windowLaplaceIntegral nodes m (halfLogWidth c t/2) := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hd0 := hd.1
  have hsmall : |halfLogWidth c t/2| *radius nodes m ≤ 1 := by
    rw [abs_of_pos (by positivity)]
    have hh := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ halfLogWidth c t/2)
    nlinarith
  have h := mellin_pole_lower nodes m hlen hm hlast (halfLogWidth c t)
    (t+halfLogWidth c t) hd.1.le hsmall
  have heq : halfLogWidth c t*exp ((t+halfLogWidth c t)/2) = poleScale c t := by
    unfold poleScale
    rw [show (t+halfLogWidth c t)/2 = t/2+halfLogWidth c t/2 by ring]
  rw [heq] at h
  have hb := pole_quadratic_loss_lt c t (nodalMu2Upper nodes m) hc hc1 ht hmu0 hmu
  nlinarith

#print axioms actual_mellin_pole_lower_domain
end RH080Next.Explicit
