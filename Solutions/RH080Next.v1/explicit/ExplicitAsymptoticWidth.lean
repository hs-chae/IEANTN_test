/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitWindowErrors
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
noncomputable section
open Real Set Filter
open scoped Topology
namespace RH080Next.Explicit

/-- Polynomial times the actual half-exponential tends to zero. -/
theorem pow_half_exp_tendsto_zero (k : ℕ) :
    Tendsto (fun t : ℝ => t^k*exp (-t/2)) atTop (𝓝 0) := by
  have h := (tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (show Tendsto (fun t : ℝ => t/2) atTop atTop from tendsto_id.atTop_div_const (by norm_num))
  have hh : Tendsto (fun t : ℝ => (2:ℝ)^k*((t/2)^k*exp (-(t/2)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using h.const_mul ((2:ℝ)^k)
  apply hh.congr
  intro t
  rw [←mul_assoc,←mul_pow,show (2:ℝ)*(t/2) = t by ring]
  congr 2 <;> ring

theorem intervalRatio_tendsto_zero (c : ℝ) :
    Tendsto (intervalRatio c) atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => c*t*exp (-t/2)) atTop (𝓝 0)
  simpa only [pow_one,mul_zero,mul_assoc] using
    (pow_half_exp_tendsto_zero 1).const_mul c

theorem halfLogWidth_tendsto_zero (c : ℝ) :
    Tendsto (halfLogWidth c) atTop (𝓝 0) := by
  have h := ((tendsto_const_nhds.add (intervalRatio_tendsto_zero c)).log (by norm_num : (1:ℝ)+0 ≠ 0)).div_const 2
  change Tendsto (fun t : ℝ => log (1+intervalRatio c t)/2) atTop (𝓝 0)
  simpa only [add_zero,log_one,zero_div] using h

/-- Uniform elementary inequalities for arbitrary fixed positive c, without
retaining the finite explicit experiment's c≤1 restriction. -/
theorem halfLogWidth_squeeze (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    0 < halfLogWidth c t ∧
    intervalRatio c t/(intervalRatio c t+2) ≤ halfLogWidth c t ∧
    halfLogWidth c t ≤ intervalRatio c t/2 := by
  have hz : 0 < intervalRatio c t := by unfold intervalRatio; positivity
  have hlo := le_log_one_add_of_nonneg hz.le
  have hhi := log_le_sub_one_of_pos (by linarith : 0 < 1+intervalRatio c t)
  unfold halfLogWidth
  refine ⟨div_pos (log_pos (by linarith)) (by norm_num),?_,by linarith⟩
  rw [show 2*intervalRatio c t/(intervalRatio c t+2) = 2*(intervalRatio c t/(intervalRatio c t+2)) by ring] at hlo
  linarith

/-- The actual Mellin width has its required first-order normalization. -/
theorem halfLogWidth_scaled_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => halfLogWidth c t*exp (t/2)/t) atTop (𝓝 (c/2)) := by
  have hlo : Tendsto (fun t : ℝ => c/(intervalRatio c t+2)) atTop (𝓝 (c/2)) := by
    change Tendsto ((fun _ : ℝ => c)/(fun t => intervalRatio c t+2)) atTop (𝓝 (c/2))
    simpa only [zero_add] using tendsto_const_nhds.div ((intervalRatio_tendsto_zero c).add_const 2) (by norm_num : (0:ℝ)+2 ≠ 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have h := (halfLogWidth_squeeze c t hc ht).2.1
    have he : intervalRatio c t*exp (t/2)/t = c := by
      unfold intervalRatio
      rw [mul_assoc,mul_assoc,←exp_add]
      simp only [show -t/2+t/2 = 0 by ring,exp_zero,mul_one]
      field_simp
    have hh := mul_le_mul_of_nonneg_right h (div_pos (exp_pos (t/2)) ht).le
    rw [show intervalRatio c t/(intervalRatio c t+2)*(exp (t/2)/t) =
      (intervalRatio c t*exp (t/2)/t)/(intervalRatio c t+2) by ring,he] at hh
    simpa only [mul_div_assoc] using hh
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have h := (halfLogWidth_squeeze c t hc ht).2.2
    have he : intervalRatio c t*exp (t/2)/t = c := by
      unfold intervalRatio
      rw [mul_assoc,mul_assoc,←exp_add]
      simp only [show -t/2+t/2 = 0 by ring,exp_zero,mul_one]
      field_simp
    have hh := mul_le_mul_of_nonneg_right h (div_pos (exp_pos (t/2)) ht).le
    rw [show intervalRatio c t/2*(exp (t/2)/t) =
      (intervalRatio c t*exp (t/2)/t)/2 by ring,he] at hh
    simpa only [mul_div_assoc] using hh

theorem poleScale_div_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t : ℝ => poleScale c t/t) atTop (𝓝 (c/2)) := by
  have hsmall : Tendsto (fun t : ℝ => halfLogWidth c t/2) atTop (𝓝 0) := by
    simpa only [zero_div] using (halfLogWidth_tendsto_zero c).div_const 2
  have hExp := (Real.continuous_exp.tendsto 0).comp hsmall
  have h := (halfLogWidth_scaled_tendsto c hc).mul hExp
  change Tendsto (fun t : ℝ => halfLogWidth c t*exp (t/2+halfLogWidth c t/2)/t) atTop (𝓝 (c/2))
  simpa only [Function.comp_def,zero_div,exp_zero,mul_one,exp_add,mul_assoc,div_mul_eq_mul_div] using h

theorem pow_mul_halfLogWidth_tendsto_zero (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun t : ℝ => t^k*halfLogWidth c t) atTop (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => (c/2)*(t^(k+1)*exp (-t/2))) atTop (𝓝 0) := by
    simpa using (pow_half_exp_tendsto_zero (k+1)).const_mul (c/2)
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact mul_nonneg (pow_nonneg ht.le k) (halfLogWidth_squeeze c t hc ht).1.le
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have h := mul_le_mul_of_nonneg_left (halfLogWidth_squeeze c t hc ht).2.2 (pow_nonneg ht.le k)
    have he : t^k*(intervalRatio c t/2)=(c/2)*(t^(k+1)*exp (-t/2)) := by unfold intervalRatio; ring
    rwa [he] at h

/-- For arbitrary fixed c>0, the zero-height logarithm is eventually bounded
by t/2. This uses a proved lower bound on the actual width. -/
theorem log_inverse_width_eventually_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, log (1/halfLogWidth c t) ≤ t/2 := by
  have hlow : ∀ᶠ t : ℝ in atTop, c/4 < halfLogWidth c t*exp (t/2)/t :=
    (tendsto_order.1 (halfLogWidth_scaled_tendsto c hc)).1 (c/4) (by linarith)
  filter_upwards [hlow,eventually_ge_atTop (4/c),eventually_gt_atTop (0:ℝ)] with t ht htc ht0
  have hd := (halfLogWidth_squeeze c t hc ht0).1
  have hprod : 1 ≤ halfLogWidth c t*exp (t/2) := by
    have hct : 1 ≤ (c/4)*t := by have h := (div_le_iff₀ hc).mp htc; nlinarith
    have hh := (lt_div_iff₀ ht0).mp ht
    linarith
  have hi : 1/halfLogWidth c t ≤ exp (t/2) := (div_le_iff₀ hd).mpr (by nlinarith)
  exact (log_le_log (by positivity) hi).trans_eq (log_exp _)

#print axioms halfLogWidth_scaled_tendsto
#print axioms pow_mul_halfLogWidth_tendsto_zero
#print axioms log_inverse_width_eventually_le
end RH080Next.Explicit
