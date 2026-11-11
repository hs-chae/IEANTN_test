/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/

import FKSComputationLed.StrongBaselineAnchor
namespace FKSComputationLed.StrongBaseline
open Real Finset MeasureTheory intervalIntegral RealBounds BaselineSound
noncomputable def G (u : ℝ) : ℝ := 2*exp (u/2)/u^2+8*exp (u/2)/u^3
noncomputable def integrand (u : ℝ) : ℝ := exp (u/2)/u^2
noncomputable def derivativeG (u : ℝ) : ℝ := integrand u-24*exp (u/2)/u^4
lemma G_deriv {u : ℝ} (hu : u≠0) : HasDerivAt G (derivativeG u) u := by
  have he : HasDerivAt (fun y:ℝ=>exp (y/2)) (exp (u/2)/2) u := by
    convert (hasDerivAt_exp (u/2)).comp u ((hasDerivAt_id u).div_const 2) using 1 <;> first | rfl | ring
  have h1 := (he.const_mul 2).div ((hasDerivAt_id u).pow 2) (pow_ne_zero 2 hu)
  have h2 := (he.const_mul 8).div ((hasDerivAt_id u).pow 3) (pow_ne_zero 3 hu)
  convert h1.add h2 using 1 <;> first | rfl | (unfold derivativeG integrand; norm_num only [Pi.pow_apply,id_eq]; field_simp [hu] <;> ring)
lemma integral_lower {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    G b-G a≤∫u in a..b,integrand u := by
  have hp : ∀u∈Set.uIcc a b,0<u := by
    intro u hu
    rw [Set.uIcc_of_le hab] at hu
    exact ha.trans_le hu.1
  have hc : ContinuousOn integrand (Set.uIcc a b) := by
    unfold integrand
    exact ((continuous_exp.comp (continuous_id.div_const 2)).continuousOn).div
      (continuous_id.pow 2).continuousOn (fun u hu=>pow_ne_zero 2 (hp u hu).ne')
  have hd : ContinuousOn derivativeG (Set.uIcc a b) := by
    unfold derivativeG
    exact hc.sub (((continuous_exp.comp (continuous_id.div_const 2)).const_mul 24).continuousOn.div
      (continuous_id.pow 4).continuousOn (fun u hu=>pow_ne_zero 4 (hp u hu).ne'))
  have hFTC : (∫u in a..b,derivativeG u)=G b-G a := by
    apply integral_eq_sub_of_hasDerivAt _ hd.intervalIntegrable
    intro u hu
    exact G_deriv (hp u hu).ne'
  rw [←hFTC]
  apply integral_mono_on hab hd.intervalIntegrable hc.intervalIntegrable
  intro u hu
  unfold derivativeG
  have hterm : 0≤24*exp (u/2)/u^4 := by positivity
  linarith
lemma exp_half_log {x : ℝ} (hx : 0<x) : exp (log x/2)=sqrt x := by
  rw [sqrt_eq_rpow,rpow_def_of_pos hx]
  congr 1
  ring
lemma G_hundred : G (log (100:ℝ))≤(5/2:ℝ) := by
  have hl := log_hundred
  unfold G
  rw [exp_half_log (by norm_num : (0:ℝ)<100)]
  norm_num
  have h2 : (16:ℝ)≤(log (100:ℝ))^2 := by nlinarith
  have h3 : (64:ℝ)≤(log (100:ℝ))^3 := by nlinarith [sq_nonneg (log (100:ℝ)-4)]
  have hd2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤20) (by norm_num : (0:ℝ)<16) h2
  have hd3 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤80) (by norm_num : (0:ℝ)<64) h3
  linarith

noncomputable def I (x : ℝ) : ℝ := ∫u in log (100:ℝ)..log x,integrand u
noncomputable def psiProfile (x : ℝ) : ℝ :=
  81/100+((81/100)*I x+anchor+BaselineTransfer.correction x)*weight x

lemma integral_weight_lower (x : ℝ) (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    (2/21:ℝ)+8/441-(5/2)*weight x≤I x*weight x := by
  have hx0 : 0<x := by linarith
  have hlog0 : 0<log x := log_pos (by linarith)
  have hL21 := log_billion hx0 hxU
  have hs0 : 0<sqrt x := sqrt_pos.mpr hx0
  have hw0 : 0≤weight x := div_nonneg hlog0.le hs0.le
  have hl := log_hundred
  have hlow := integral_lower (by linarith : 0<log (100:ℝ))
    (log_le_log (by norm_num : (0:ℝ)<100) (by linarith : (100:ℝ)≤x))
  have hmul := mul_le_mul_of_nonneg_right hlow hw0
  have heq : G (log x)*weight x=2/log x+8/(log x)^2 := by
    unfold G weight
    rw [exp_half_log hx0]
    field_simp <;> ring
  have hG := mul_le_mul_of_nonneg_right G_hundred hw0
  have hd1 : (2/21:ℝ)≤2/log x := by
    apply (le_div_iff₀ hlog0).mpr
    linarith
  have hd2 : (8/441:ℝ)≤8/(log x)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlog0)).mpr
    have hh : (log x)^2≤441 := by nlinarith [sq_nonneg (21-log x)]
    nlinarith
  dsimp [I]
  nlinarith

theorem psi_profile_two (x : ℝ) (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    (2:ℝ)≤psiProfile x := by
  have hx0 : 0<x := by linarith
  have hlog0 : 0<log x := log_pos (by linarith)
  have hL21 := log_billion hx0 hxU
  have hs0 : 0<sqrt x := sqrt_pos.mpr hx0
  have hs : (10000:ℝ)≤ sqrt x := (le_sqrt (by norm_num) hx0.le).mpr (by norm_num;exact hx)
  have hw0 : 0≤weight x := div_nonneg hlog0.le hs0.le
  have hw : weight x≤(21/10000:ℝ) := by
    unfold weight
    exact (div_le_div_of_nonneg_right hL21 hs0.le).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs)
  have hsq := (square_comparison x hx hxU).1
  unfold squareLower at hsq
  have hcor := mul_le_mul_of_nonneg_right
    (sub_le_sub_right (BaselineTransfer.correction_ge_square x) 2) hw0
  have ha := mul_le_mul_of_nonneg_right anchor_lower hw0
  have hi := integral_weight_lower x hx hxU
  unfold psiProfile
  nlinarith

/-- Corrected uniform at-least5percent comparison including the stronger old
equation6.2 ψ=.81 partial-summation route, not just Theorem2's displayed bounds. -/
theorem stronger_old_profiles_five_percent (x : ℝ)
    (hx : (100000000:ℝ)≤x) (hxU : x≤1000000000) :
    (19/10:ℝ)≤(95/100)*min (psiProfile x)
      (min (BaselineTransfer.fullStarLower x) (directLower x)) := by
  have hp := psi_profile_two x hx hxU
  have hprev := BaselineTransfer.full_old_profiles_comparison x hx hxU
  have hmin : (2:ℝ)≤ min (BaselineTransfer.fullStarLower x) (directLower x) := by linarith
  have hm := le_min hp hmin
  nlinarith

#print axioms G_deriv
#print axioms integral_lower
#print axioms stronger_old_profiles_five_percent
end FKSComputationLed.StrongBaseline
