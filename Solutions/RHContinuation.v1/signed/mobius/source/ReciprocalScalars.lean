/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
namespace RHContinuation.ReciprocalScalars
open Real Finset

lemma log_height_bound : Real.log (52000004:ℝ)<17.8 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
  apply lt_of_pow_lt_pow_left₀ 5 (Real.exp_pos _).le
  have he : (Real.exp (17.8:ℝ))^5=Real.exp 89 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [he]
  calc (52000004:ℝ)^5 < (2.7182818283:ℝ)^89 := by norm_num
    _ < (Real.exp 1)^89 := by gcongr; exact Real.exp_one_gt_d9
    _ = Real.exp 89 := by rw [← Real.exp_nat_mul]; norm_num

lemma log_compact_ratio_bound : 2*Real.log (55/48:ℝ)<0.273 := by
  have hl : Real.log (55/48:ℝ)<0.1365 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤0.1365) 5
    norm_num [Finset.sum_range_succ,Nat.factorial_succ] at h
    linarith
  linarith

noncomputable def compactBudget : ℝ :=
  (45/2)*Real.exp ((Real.log (52000004:ℝ)/5+31/8)*
    (2*Real.log (55/48:ℝ)) + (9/10:ℝ)*((55/100:ℝ)^2-(48/100:ℝ)^2)/
      ((52000002:ℝ)*52000004))

/-- Whole-compact analytic budget; every scalar bound is kernel checked. -/
theorem compact_budget_lt_180 : compactBudget<180 := by
  have hk0 : 0<2*Real.log (55/48:ℝ) := by positivity
  have hk := log_compact_ratio_bound
  have hR : Real.log (52000004:ℝ)/5+31/8 < 7.435 := by
    linarith [log_height_bound]
  have htail : (9/10:ℝ)*((55/100:ℝ)^2-(48/100:ℝ)^2)/
      ((52000002:ℝ)*52000004) < 1/10^12 := by norm_num
  have he : (Real.log (52000004:ℝ)/5+31/8)*(2*Real.log (55/48:ℝ))+
      (9/10:ℝ)*((55/100:ℝ)^2-(48/100:ℝ)^2)/
        ((52000002:ℝ)*52000004) < 2.03 := by
    nlinarith
  have hlog : (2.03:ℝ)<3*Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hexp : Real.exp ((Real.log (52000004:ℝ)/5+31/8)*
      (2*Real.log (55/48:ℝ))+(9/10:ℝ)*((55/100:ℝ)^2-(48/100:ℝ)^2)/
      ((52000002:ℝ)*52000004)) < 8 := by
    calc _ < Real.exp (3*Real.log 2) := Real.exp_lt_exp.mpr (he.trans hlog)
      _ = 8 := by
        have hh := Real.exp_nat_mul (Real.log 2) 3
        rw [Real.exp_log (by norm_num)] at hh
        norm_num at hh
        exact hh
  dsimp [compactBudget]
  nlinarith

lemma log_global_ratio_bound : 2*Real.log (11/5:ℝ)<1.58 := by
  have hl : Real.log (11/5:ℝ)<0.79 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤0.79) 7
    norm_num [Finset.sum_range_succ,Nat.factorial_succ] at h
    linarith
  linarith

lemma exp_six_point_two_lt : Real.exp (6.2:ℝ)<500 := by
  apply lt_of_pow_lt_pow_left₀ 5 (by norm_num : (0:ℝ)≤500)
  have he : (Real.exp (6.2:ℝ))^5=Real.exp 31 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [he]
  calc Real.exp 31 = (Real.exp 1)^31 := by rw [← Real.exp_nat_mul]; norm_num
    _ < (2.7182818286:ℝ)^31 := by gcongr; exact Real.exp_one_lt_d9
    _ < (500:ℝ)^5 := by norm_num

lemma six_rpow_point32_lt_two : (6:ℝ)^(0.32:ℝ)<2 := by
  have hl6 : Real.log 6<1.8 := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9,Real.log_three_lt_d9]
  rw [Real.rpow_def_of_pos (by norm_num)]
  have he : Real.log 6*0.32<Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hh := Real.exp_lt_exp.mpr he
  simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using hh

/-- The global coefficient for sigma=.75. This validates the analytic envelope's
scalar part; it is not a theorem assuming or asserting a new zeta numerical input. -/
noncomputable def globalBudget (t : ℝ) : ℝ :=
  147*Real.exp ((Real.log (2*t+4)/5+31/8)*(2*Real.log (11/5:ℝ))+
    (9/10:ℝ)*((55/100:ℝ)^2-(25/100:ℝ)^2)/((2*t+2)*(2*t+4)))

theorem global_budget_le {t:ℝ} (ht:1≤t) :
    globalBudget t < 150000*t^(0.32:ℝ) := by
  have ht0 : 0<t := by linarith
  have hk0 : 0<2*Real.log (11/5:ℝ) := by positivity
  have hk := log_global_ratio_bound
  have hden : (8:ℝ)≤(2*t+2)*(2*t+4) := by nlinarith
  have htail : (9/10:ℝ)*((55/100:ℝ)^2-(25/100:ℝ)^2)/((2*t+2)*(2*t+4))≤0.027 := by
    apply (div_le_iff₀ (by positivity : 0<(2*t+2)*(2*t+4))).mpr
    nlinarith
  have hlogt : 0≤Real.log t := Real.log_nonneg ht
  have hlog6 : 0<Real.log 6 := Real.log_pos (by norm_num)
  have hlogs : Real.log (2*t+4)≤Real.log 6+Real.log t := by
    rw [← Real.log_mul (by norm_num) ht0.ne']
    exact Real.log_le_log (by positivity) (by linarith)
  have hExp : (Real.log (2*t+4)/5+31/8)*(2*Real.log (11/5:ℝ))+
      (9/10:ℝ)*((55/100:ℝ)^2-(25/100:ℝ)^2)/((2*t+2)*(2*t+4))
      < 6.2+0.32*(Real.log 6+Real.log t) := by
    nlinarith
  have hbound : Real.exp ((Real.log (2*t+4)/5+31/8)*(2*Real.log (11/5:ℝ))+
      (9/10:ℝ)*((55/100:ℝ)^2-(25/100:ℝ)^2)/((2*t+2)*(2*t+4))) <
      1000*t^(0.32:ℝ) := by
    calc _ < Real.exp (6.2+0.32*(Real.log 6+Real.log t)) := Real.exp_lt_exp.mpr hExp
      _ = Real.exp 6.2*((6:ℝ)^(0.32:ℝ)*t^(0.32:ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num),Real.rpow_def_of_pos ht0,
          ← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      _ < 500*(2*t^(0.32:ℝ)) := by
        gcongr
        · exact exp_six_point_two_lt
        · exact six_rpow_point32_lt_two
      _ = 1000*t^(0.32:ℝ) := by ring
  dsimp [globalBudget]
  have hpow : 0<t^(0.32:ℝ) := Real.rpow_pos_of_pos ht0 _
  nlinarith

#print axioms compact_budget_lt_180
#print axioms global_budget_le
end RHContinuation.ReciprocalScalars
