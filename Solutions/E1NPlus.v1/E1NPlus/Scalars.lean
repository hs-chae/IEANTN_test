/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1FrozenN.Final
namespace E1NPlus
open Real
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 1000

theorem log_upper_of_power {r:ℝ} (hr:0<r) (a b:ℕ)
    (h:r^b≤(2.7182818283:ℝ)^a) : (b:ℝ)*log r≤a := by
  have hp:=h.trans (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2.7182818283) exp_one_gt_d9.le a)
  have hl:=log_le_log (pow_pos hr b) hp
  simpa only [log_pow,log_exp,mul_one] using hl

theorem log_lower_of_power {r:ℝ} (hr:0<r) (a b:ℕ)
    (h:(2.7182818286:ℝ)^a≤r^b) : (a:ℝ)≤(b:ℝ)*log r := by
  have hp:=(pow_le_pow_left₀ (exp_pos (1:ℝ)).le exp_one_lt_d9.le a).trans h
  have hl:=log_le_log (pow_pos (exp_pos (1:ℝ)) a) hp
  simpa only [log_pow,log_exp,mul_one] using hl

noncomputable def k : ℝ := 2001/860
noncomputable def a1 : ℝ := 67829/500
noncomputable def a2 : ℝ := 67719/500
noncomputable def a3 : ℝ := 16486/125
noncomputable def g4 (q z:ℝ) : ℝ :=
  1+q/z+q*(q-1)/z^2+q*(q-1)*(q-2)/z^3+q*(q-1)*(q-2)*(q-3)/z^4

 theorem log_k_bounds : (7/10:ℝ)≤log k ∧ log k≤17/20 := by
  have hl:=log_lower_of_power (r:=k) (by norm_num [k]) 7 10 (by norm_num [k])
  have hu:=log_upper_of_power (r:=k) (by norm_num [k]) 17 20 (by norm_num [k])
  norm_num at hl hu
  constructor <;> linarith

 theorem exp18_15_lower : (76250000:ℝ)≤exp (363/20:ℝ) := by
  have hl:=log_upper_of_power (r:=76250000) (by norm_num) 363 20 (by norm_num)
  norm_num at hl
  have hh:log (76250000:ℝ)≤363/20 := by linarith
  simpa only [exp_log (by norm_num : (0:ℝ)<76250000)] using exp_le_exp.mpr hh

 theorem exp_neg_a1_lower : (183/1000:ℝ)≤exp (-(a1/80)) := by
  have hl:=log_lower_of_power (r:=1000/183) (by norm_num) 212 125 (by norm_num)
  have hh:a1/80≤log (1000/183:ℝ) := by norm_num [a1] at hl ⊢;linarith
  have he:=exp_le_exp.mpr hh
  rw [exp_log (by norm_num : (0:ℝ)<1000/183)] at he
  rw [exp_neg,←one_div]
  apply (le_div_iff₀ (exp_pos _)).mpr
  nlinarith

 theorem exp_neg_a2_upper : exp (-(a2/80))≤(185/1000:ℝ) := by
  have hl:=log_upper_of_power (r:=200/37) (by norm_num) 169 100 (by norm_num)
  have hh:log (200/37:ℝ)≤a2/80 := by norm_num [a2] at hl ⊢;linarith
  have he:=exp_le_exp.mpr hh
  rw [exp_log (by norm_num : (0:ℝ)<200/37)] at he
  rw [exp_neg,←one_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  nlinarith

 theorem exp_neg_a2_double_lower : (337/10000:ℝ)≤exp (-(a2/40)) := by
  have hl:=log_lower_of_power (r:=10000/337) (by norm_num) 339 100 (by norm_num)
  have hh:a2/40≤log (10000/337:ℝ) := by norm_num [a2] at hl ⊢;linarith
  have he:=exp_le_exp.mpr hh
  rw [exp_log (by norm_num : (0:ℝ)<10000/337)] at he
  rw [exp_neg,←one_div]
  apply (le_div_iff₀ (exp_pos _)).mpr
  nlinarith

 theorem exp_neg_a3_upper : exp (-(a3/40))≤(373/10000:ℝ) := by
  have hl:=log_upper_of_power (r:=10000/373) (by norm_num) 329 100 (by norm_num)
  have hh:log (10000/373:ℝ)≤a3/40 := by norm_num [a3] at hl ⊢;linarith
  have he:=exp_le_exp.mpr hh
  rw [exp_log (by norm_num : (0:ℝ)<10000/373)] at he
  rw [exp_neg,←one_div]
  apply (div_le_iff₀ (exp_pos _)).mpr
  nlinarith

 theorem exp13_2_lower : (530000:ℝ)≤exp (66/5:ℝ) := by
  have hl:=log_upper_of_power (r:=530000) (by norm_num) 66 5 (by norm_num)
  norm_num at hl
  have hh:log (530000:ℝ)≤66/5 := by linarith
  simpa only [exp_log (by norm_num : (0:ℝ)<530000)] using exp_le_exp.mpr hh

 theorem log_u_upper : log (1403/20:ℝ)≤4251/1000 := by
  have hl:=log_upper_of_power (r:=701/10) (by norm_num) 17 4 (by norm_num)
  have he:(701/10:ℝ)≤exp (17/4:ℝ) := by
    have hh:log (701/10:ℝ)≤17/4 := by linarith
    simpa only [exp_log (by norm_num : (0:ℝ)<701/10)] using exp_le_exp.mpr hh
  have he2:=add_one_le_exp (1/1000:ℝ)
  have hm:=mul_le_mul he he2 (by norm_num : (0:ℝ)≤1/1000+1) (exp_pos _).le
  have heq:exp (17/4:ℝ)*exp (1/1000:ℝ)=exp (4251/1000:ℝ) := by rw [←exp_add];congr 1;norm_num
  rw [heq] at hm
  have hh:(1403/20:ℝ)≤exp (4251/1000:ℝ) := by linarith
  simpa only [log_exp] using log_le_log (by norm_num : (0:ℝ)<1403/20) hh

 theorem log_v_coefficient_upper : log (396000000/43:ℝ)≤161/10 := by
  have hl:=log_upper_of_power (r:=396000000/43) (by norm_num) 161 10 (by norm_num)
  linarith

 theorem high_three_case_arithmetic :
    (3*(72091/10000)*330*(663/500)*(1403/20)^3*(579/200)/76250000:ℝ)*
      (g4 (131/40) (133/3)*((817/1000)/a1)+
       g4 (33/10) 42*((1513/10000)/a2)+g4 (7/2) (70/3)*((373/10000)/a3))<997/1000 := by
  norm_num [g4,a1,a2,a3]

 theorem low_arithmetic :
    ((234/100)/3/530000*((427/5)+((427/5)^2-70^2)/2):ℝ)<19/10000 := by norm_num
#print axioms high_three_case_arithmetic
#print axioms exp18_15_lower
end E1NPlus
