/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
/- Uniform real scalar part of the horizontal contour estimate. -/
import ReciprocalScalars
import Mathlib.Tactic
namespace RHContinuation.StripScalars
open Real RHContinuation.ReciprocalScalars
noncomputable def stripBudget (sigma t:ℝ) : ℝ :=
  (21*max 1 ((1-sigma)/(1/20))*((21/20)/sigma))*
  Real.exp ((Real.log (2*t+4)/5+31/8)*
    (2*Real.log ((11/20)/(sigma-1/2)))+
    (9/10:ℝ)*((11/20:ℝ)^2-(sigma-1/2)^2)/((2*t+2)*(2*t+4)))

theorem uniform_strip {sigma t:ℝ} (hs:3/4≤sigma) (hs1:sigma≤21/20) (ht:0≤t) :
    stripBudget sigma t≤globalBudget t := by
  have hs0 : 0<sigma := by linarith
  have ha : 0<sigma-1/2 := by linarith
  have hmax : max (1:ℝ) ((1-sigma)/(1/20))≤5 := by
    apply max_le (by norm_num)
    norm_num
    linarith
  have hratio : ((21/20:ℝ)/sigma)≤7/5 := by
    apply (div_le_iff₀ hs0).mpr
    linarith
  have hpref : 21*max (1:ℝ) ((1-sigma)/(1/20))*((21/20)/sigma)≤147 := by
    have hm : 0≤max (1:ℝ) ((1-sigma)/(1/20)) := le_trans (by norm_num) (le_max_left _ _)
    nlinarith
  have hk : 2*Real.log ((11/20:ℝ)/(sigma-1/2))≤2*Real.log (11/5:ℝ) := by
    have hq : (11/20:ℝ)/(sigma-1/2)≤11/5 := by
      apply (div_le_iff₀ ha).mpr
      linarith
    gcongr
  have hR : 0≤Real.log (2*t+4)/5+31/8 := by
    have hl := Real.log_nonneg (show 1≤2*t+4 by linarith)
    linarith
  have hd : (11/20:ℝ)^2-(sigma-1/2)^2≤(55/100:ℝ)^2-(25/100:ℝ)^2 := by
    nlinarith
  have hexp : Real.exp ((Real.log (2*t+4)/5+31/8)*
      (2*Real.log ((11/20:ℝ)/(sigma-1/2)))+
      (9/10:ℝ)*((11/20:ℝ)^2-(sigma-1/2)^2)/((2*t+2)*(2*t+4))) ≤
      Real.exp ((Real.log (2*t+4)/5+31/8)*(2*Real.log (11/5:ℝ))+
      (9/10:ℝ)*((55/100:ℝ)^2-(25/100:ℝ)^2)/((2*t+2)*(2*t+4))) := by
    apply Real.exp_le_exp.mpr
    gcongr
  unfold stripBudget globalBudget
  exact mul_le_mul hpref hexp (Real.exp_pos _).le (by norm_num)

theorem global_budget_small {t:ℝ} (ht:0≤t) (ht1:t≤1) : globalBudget t<150000 := by
  have hk0 : 0<2*Real.log (11/5:ℝ) := by positivity
  have hk := log_global_ratio_bound
  have hden : (8:ℝ)≤(2*t+2)*(2*t+4) := by nlinarith
  have htail : (9/10:ℝ)*((55/100:ℝ)^2-(25/100:ℝ)^2)/((2*t+2)*(2*t+4))≤0.027 := by
    apply (div_le_iff₀ (by positivity : 0<(2*t+2)*(2*t+4))).mpr
    nlinarith
  have hlog6 : 0<Real.log 6 := Real.log_pos (by norm_num)
  have hl : Real.log (2*t+4)≤Real.log 6 := Real.log_le_log (by positivity) (by linarith)
  have he : (Real.log (2*t+4)/5+31/8)*(2*Real.log (11/5:ℝ))+
      (9/10:ℝ)*((55/100:ℝ)^2-(25/100:ℝ)^2)/((2*t+2)*(2*t+4)) <6.2+0.32*Real.log 6 := by
    nlinarith
  have hx : Real.exp (6.2+0.32*Real.log 6)<1000 := by
    calc
      Real.exp (6.2+0.32*Real.log 6) = Real.exp 6.2*(6:ℝ)^(0.32:ℝ) := by
        rw [Real.rpow_def_of_pos (by norm_num),← Real.exp_add]
        congr 1
        ring
      _ < 500*2 := by gcongr; exact exp_six_point_two_lt; exact six_rpow_point32_lt_two
      _ = 1000 := by norm_num
  have hx' := (Real.exp_lt_exp.mpr he).trans hx
  unfold globalBudget
  nlinarith
#print axioms uniform_strip
#print axioms global_budget_small
end RHContinuation.StripScalars
