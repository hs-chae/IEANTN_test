/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalSharpScalars
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
namespace WinnerOriginalScalars
open Real
set_option maxHeartbeats 0

/-- KLN(4.10), k=1, with the paper's Euler constant kept explicit. -/
noncomputable def sourceCFive (gamma : ℝ) : ℝ :=
  Real.pi*sourceM0*(529/1000)/(2*(3119/10000))*
    (1+2*(3119/10000)/log height)^2*exp (2*(3119/10000)*gamma/log height)
/-- KLN(4.11), k=1. -/
noncomputable def sourceCSix : ℝ :=
  (529/1000)/(5*(3119/10000)*exp (3119/10000))*
    (1+(3119/10000)/log height)^2+
    (121/200)*exp (-2*(3119/10000))/(log height)^2
/-- KLN(4.19)--(4.20), beta=2 and k=1, using its exact Gaussian moments. -/
noncomputable def sourceRightV (gamma T : ℝ) : ℝ :=
  8*(601/5000)*exp (2*(601/5000)*((1+(3119/10000)/log T)/T)^2)*
    ((sourceCFive gamma+sourceCSix*Real.pi*sourceM0/T)/(4*(601/5000))+
      sourceCSix*sqrt Real.pi/(8*(601/5000)*sqrt (2*(601/5000))))

 theorem cFive_semantics : value cFive=sourceCFive 1 := by
  simp [cFive,sourceCFive,delta,mzero_semantics,log_semantics]
  ring

 theorem cSix_semantics : value cSix=sourceCSix := by
  simp [cSix,sourceCSix,delta,log_semantics]

 theorem rightV_semantics : value rightV=sourceRightV 1 height := by
  unfold rightV
  simp only [value_mul,value_add,value_div,value_exp,value_sq,value_lit,value_inv,
    value_pi,cFive_semantics,cSix_semantics,mzero_semantics]
  rw [value_rt _ (by simpa using Real.pi_pos), value_rt _ (by norm_num [alpha])]
  simp only [value_mul,value_lit,alpha,delta,log_semantics,height_semantics]
  norm_num [sourceRightV,height,value_pi]
  ring

 theorem source_rightV_height_upper : sourceRightV 1 height≤17/2 := by
  rw [←rightV_semantics]
  exact rightV_upper

 theorem source_mzero_pos : 0<sourceM0 := by unfold sourceM0; positivity
 theorem source_cfive_nonneg (gamma : ℝ) : 0≤sourceCFive gamma := by
  have hM0:=source_mzero_pos
  unfold sourceCFive
  positivity
 theorem source_csix_nonneg : 0≤sourceCSix := by unfold sourceCSix; positivity

 theorem source_cfive_gamma_le {gamma : ℝ} (hg : gamma≤1) :
    sourceCFive gamma≤sourceCFive 1 := by
  have hh : 0<log height := by linarith [source_log_lower]
  have hM0:=source_mzero_pos
  unfold sourceCFive
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply exp_le_exp.mpr
  apply div_le_div_of_nonneg_right _ hh.le
  nlinarith

/-- Uniform applicability is proved directly, rather than hidden in a new constant oracle. -/
 theorem source_rightV_uniform {gamma T : ℝ} (hg : gamma≤1) (hT : height≤T) :
    sourceRightV gamma T≤sourceRightV 1 height := by
  have hH : 0<height := by norm_num [height]
  have hTp : 0<T := lt_of_lt_of_le hH hT
  have hh : 0<log height := by linarith [source_log_lower]
  have hlog : log height≤log T := log_le_log hH hT
  have hlogp : 0<log T := lt_of_lt_of_le hh hlog
  have hd : (3119/10000:ℝ)/log T≤(3119/10000)/log height := by gcongr
  have hs : (1+(3119/10000)/log T)/T≤(1+(3119/10000)/log height)/height := by
    gcongr
  have hs0 : 0≤(1+(3119/10000)/log T)/T := by positivity
  have he : exp (2*(601/5000)*((1+(3119/10000)/log T)/T)^2)≤
      exp (2*(601/5000)*((1+(3119/10000)/log height)/height)^2) := by
    apply exp_le_exp.mpr
    gcongr
  have hm : sourceCSix*Real.pi*sourceM0/T≤sourceCSix*Real.pi*sourceM0/height := by
    apply div_le_div_of_nonneg_left (by positivity [source_csix_nonneg,source_mzero_pos]) hH hT
  have hC5:=source_cfive_nonneg gamma
  have hC6:=source_csix_nonneg
  have hM0:=source_mzero_pos
  unfold sourceRightV
  apply mul_le_mul _ _ (by positivity)
    (by positivity)
  · exact mul_le_mul_of_nonneg_left he (by norm_num)
  · gcongr
    exact source_cfive_gamma_le hg

 theorem euler_gamma_le_one : eulerMascheroniConstant≤1 := by
  linarith [eulerMascheroniConstant_lt_two_thirds]

 theorem published_rightV_upper {T : ℝ} (hT : height≤T) :
    sourceRightV eulerMascheroniConstant T≤17/2 :=
  (source_rightV_uniform euler_gamma_le_one hT).trans source_rightV_height_upper

/-- Consumer of the independently sourced KLN Lemma4.7, not a new chosen-V hypothesis. -/
 theorem right_moment_upper {Mright : ℝ→ℝ} {T : ℝ} (hT : height≤T)
    (hSource : Mright T≤sourceRightV eulerMascheroniConstant T*(log T)^2) :
    Mright T≤(17/2)*(log T)^2 := by
  exact hSource.trans (mul_le_mul_of_nonneg_right (published_rightV_upper hT) (sq_nonneg _))

#print axioms right_moment_upper
#print axioms published_rightV_upper
end WinnerOriginalScalars
