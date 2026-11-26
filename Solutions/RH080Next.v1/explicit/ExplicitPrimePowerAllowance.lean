/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitWindowErrors

set_option autoImplicit false
noncomputable section
open Real
namespace RH080Next.Explicit

private theorem exp_small_radius (c t R : ℝ) (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1)
    (ht : 42 ≤ t) (hR0 : 0 ≤ R) (hR : R ≤ 10) :
    exp (R*halfLogWidth c t/2) ≤ (101/100:ℝ) := by
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hd0 := hd.1.le
  have hq0 : 0 ≤ R*halfLogWidth c t/2 := by positivity
  have hq : R*halfLogWidth c t/2 ≤ (1/10000000:ℝ) := by nlinarith
  have he := exp_bound_div_one_sub_of_interval hq0 (by linarith : R*halfLogWidth c t/2 < 1)
  have hden : 0 < 1-R*halfLogWidth c t/2 := by linarith
  apply he.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith

/-- The narrow prime-power window bound is less than 0.001 on the entire
original continuous parameter domain, with radius seven genuinely included.
This proves the scalar specialization of the separate actual prime-power
counting theorem; that counting theorem is not assumed by this lemma. -/
theorem primepower_window_allowance_lt (c t R M : ℝ)
    (hc : (1/2:ℝ) ≤ c) (hc1 : c ≤ 1) (ht : 42 ≤ t)
    (hR0 : 0 ≤ R) (hR : R ≤ 10) (hM0 : 0 ≤ M) (hM : M ≤ 2) :
    M*(t+(1+R)*halfLogWidth c t)^2/
      (2*log 2*exp ((t+(1-R)*halfLogWidth c t)/2))*
      (1+R*halfLogWidth c t*exp ((t+(1+R)*halfLogWidth c t)/2)) < (1/1000:ℝ) := by
  let d := halfLogWidth c t
  let α : ℝ := 101/100
  have hd := halfLogWidth_bounds c t hc hc1 ht
  have hd0 : 0 ≤ d := hd.1.le
  have ht0 : 0 ≤ t := by linarith
  have hlog : (1/2:ℝ) ≤ log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h
    exact h
  have hlog0 : 0 < log 2 := by linarith
  have hexp := exp_small_radius c t R hc hc1 ht hR0 hR
  have hexp' : exp ((R-1)*d/2) ≤ α := by
    apply (exp_le_exp.mpr (by dsimp [d]; nlinarith)).trans hexp
  have hlinear : 0 ≤ t+(1+R)*d := by positivity
  have hlinearCap : t+(1+R)*d ≤ α*t := by dsimp [α,d]; nlinarith
  have hsq := pow_le_pow_left₀ hlinear hlinearCap 2
  have hp := poleScale_upper c t hc hc1 ht
  have hp0 : 0 ≤ poleScale c t := by unfold poleScale; positivity
  have hinside : 1+R*d*exp ((t+(1+R)*d)/2) ≤ 1+5*α*t := by
    have hex : exp ((t+(1+R)*d)/2) = exp (t/2+d/2)*exp (R*d/2) := by
      rw [←exp_add]
      congr 1
      ring
    have heq : R*d*exp ((t+(1+R)*d)/2) = R*poleScale c t*exp (R*d/2) := by
      rw [hex]
      unfold poleScale
      dsimp [d]
      ring
    rw [heq]
    have hpcap : R*poleScale c t ≤ 5*t := by
      have hp' : poleScale c t ≤ t/2 := hp.trans (by nlinarith)
      have hh := mul_le_mul hR hp' hp0 (by norm_num : (0:ℝ)≤10)
      nlinarith
    have hh := mul_le_mul hpcap hexp (exp_pos _).le (by positivity : (0:ℝ)≤5*t)
    dsimp [α] at hh ⊢
    nlinarith
  have hdenEq : M*(t+(1+R)*d)^2/(2*log 2*exp ((t+(1-R)*d)/2)) =
      (M/(2*log 2))*(t+(1+R)*d)^2*exp (-t/2)*exp ((R-1)*d/2) := by
    calc
      _ = (M/(2*log 2))*(t+(1+R)*d)^2*exp (-((t+(1-R)*d)/2)) := by
        rw [exp_neg]
        ring
      _ = _ := by
        rw [show -((t+(1-R)*d)/2) = -t/2+(R-1)*d/2 by ring,exp_add]
        ring
  have hMcap : M/(2*log 2) ≤ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*log 2)).mpr
    nlinarith
  have hMpos : 0 ≤ M/(2*log 2) := by positivity
  have hpref : M*(t+(1+R)*d)^2/(2*log 2*exp ((t+(1-R)*d)/2)) ≤
      2*α^3*t^2*exp (-t/2) := by
    rw [hdenEq]
    have h1 := mul_le_mul hMcap hsq (sq_nonneg _) (by norm_num : (0:ℝ)≤2)
    have h2 := mul_le_mul_of_nonneg_right h1 (exp_pos (-t/2)).le
    have h3 := mul_le_mul h2 hexp' (exp_pos _).le (by positivity : 0≤2*(α*t)^2*exp (-t/2))
    calc
      _ ≤ 2*(α*t)^2*exp (-t/2)*α := h3
      _ = _ := by ring
  have hinside0 : 0 ≤ 1+R*d*exp ((t+(1+R)*d)/2) := by positivity
  have hmain := mul_le_mul hpref hinside hinside0 (by dsimp [α]; positivity : 0≤2*α^3*t^2*exp (-t/2))
  have heq : (2*α^3*t^2*exp (-t/2))*(1+5*α*t) =
      2*α^3*(t^2*exp (-t/2))+10*α^4*(t^3*exp (-t/2)) := by ring
  rw [heq] at hmain
  have h2 := polynomial_exp_decay t ht 2 (by norm_num) (by norm_num)
  have h3 := polynomial_exp_decay t ht 3 (by norm_num) (by norm_num)
  have hh2 := mul_le_mul_of_nonneg_left h2 (by dsimp [α]; positivity : 0≤2*α^3)
  have hh3 := mul_le_mul_of_nonneg_left h3 (by dsimp [α]; positivity : 0≤10*α^4)
  have he := exp_neg_twenty_one_upper
  dsimp [α] at hh2 hh3
  change M*(t+(1+R)*d)^2/(2*log 2*exp ((t+(1-R)*d)/2))*
      (1+R*d*exp ((t+(1+R)*d)/2)) < _
  nlinarith

#print axioms primepower_window_allowance_lt
end RH080Next.Explicit
