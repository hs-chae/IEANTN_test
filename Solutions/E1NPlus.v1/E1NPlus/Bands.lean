/- Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import E1NPlus.Ray
namespace E1NPlus
open Real Set
set_option maxHeartbeats 0

theorem g4_mono {q Q z Z:ℝ} (hq:3≤q) (hQ:q≤Q) (hZ:0<Z) (hz:Z≤z) :
    g4 q z≤g4 Q Z := by
  have hq0:0≤q:=by linarith
  have hq1:0≤q-1:=by linarith
  have hq2:0≤q-2:=by linarith
  have hq3:0≤q-3:=by linarith
  have hQ0:0≤Q:=by linarith
  have hQ1:0≤Q-1:=by linarith
  have hQ2:0≤Q-2:=by linarith
  have hQ3:0≤Q-3:=by linarith
  unfold g4
  gcongr <;> first | positivity | linarith

theorem reciprocal_band {d a:ℝ} (hd:0≤d) (hda:d≤a) (ha:a<1/4) :
    1/(1-4*d)≤exp ((4/(1-4*a))*d) := by
  have hya:0<1-4*a:=by linarith
  have hyd:0<1-4*d:=by linarith
  have hdiv:=div_le_div_of_nonneg_left (show 0≤4*d by positivity) hya (show 1-4*a≤1-4*d by linarith)
  have hid:1/(1-4*d)=1+4*d/(1-4*d) := by field_simp;ring
  rw [hid]
  calc
    _ ≤ 1+4*d/(1-4*a) := by linarith
    _ = (4/(1-4*a))*d+1 := by ring
    _ ≤ _ := add_one_le_exp _

theorem k_cube_root_upper : exp (log k/3)≤(663/500:ℝ) := by
  have hp:k≤(663/500:ℝ)^3:=by norm_num [k]
  have hl:=log_le_log (by norm_num [k] : 0<k) hp
  rw [log_pow] at hl
  norm_num at hl
  have hh:log k/3≤log (663/500:ℝ):=by linarith
  simpa only [exp_log (by norm_num : (0:ℝ)<663/500)] using exp_le_exp.mpr hh

theorem u_quarter_root_upper {u:ℝ} (hu:0<u) (huu:u≤1403/20) :
    exp (log u/4)≤(579/200:ℝ) := by
  have hp:u≤(579/200:ℝ)^4:=by nlinarith
  have hl:=log_le_log hu hp
  rw [log_pow] at hl
  norm_num at hl
  have hh:log u/4≤log (579/200:ℝ):=by linarith
  simpa only [exp_log (by norm_num : (0:ℝ)<579/200)] using exp_le_exp.mpr hh

theorem u330_bounds : (70:ℝ)≤ulog 330 ∧ ulog 330≤1403/20 := by
  have hh:=log_k_bounds
  constructor <;> dsimp [ulog,eta] <;> linarith [hh.1,hh.2]

theorem log_u330_upper : log (ulog 330)≤4251/1000 := by
  have hh:=log_le_log (by linarith [u330_bounds.1] : 0<ulog 330) u330_bounds.2
  exact hh.trans log_u_upper

theorem inverse_exp18 : exp (-(363/20:ℝ))≤1/76250000 := by
  rw [exp_neg,←one_div]
  exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)<76250000) exp18_15_lower

noncomputable def mainPref : ℝ :=
  3*K*330*(663/500)*(1403/20)^3*(579/200)/76250000
noncomputable def nearG : ℝ :=g4 (131/40) (133/3)
noncomputable def midG : ℝ :=g4 (33/10) 42
noncomputable def farG : ℝ :=g4 (7/2) (70/3)

theorem main_three_case_tight :
    mainPref*(nearG*((817/1000)/a1)+midG*((1513/10000)/a2)+farG*((373/10000)/a3))<9962/10000 := by
  norm_num [mainPref,K,nearG,midG,farG,g4,a1,a2,a3]

#print axioms reciprocal_band
#print axioms main_three_case_tight
end E1NPlus
