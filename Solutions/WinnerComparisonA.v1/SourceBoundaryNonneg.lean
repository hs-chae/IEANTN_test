/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OriginalBoundaryScalars
namespace WinnerOriginalScalars
open Real
set_option maxHeartbeats 0

theorem bfive_ge_one : 1 ≤ sourceBFive := by
  have h1:=positiveZeta_lower (s:=1+boundaryEta) (by norm_num [boundaryEta])
  have h2:=positiveZeta_lower (s:=2+2*boundaryEta) (by norm_num [boundaryEta])
  have h2u : positiveZeta (2+2*boundaryEta) ≤ 2 := by
    have h:=positiveZeta_upper (s:=2+2*boundaryEta) (by norm_num [boundaryEta])
    norm_num [boundaryEta] at h ⊢
    linarith
  have hp : 0<positiveZeta (2+2*boundaryEta) := by linarith
  have ht : 1 ≤ 2*positiveZeta (1+boundaryEta)^2/positiveZeta (2+2*boundaryEta) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith [sq_nonneg (positiveZeta (1+boundaryEta)-1)]
  unfold sourceBFive
  have hh : 0 ≤ positiveZeta (1+boundaryEta)^4/positiveZeta (2+2*boundaryEta)^2 := by positivity
  linarith

theorem bseven_ge_one : 1 ≤ sourceBSeven := by
  have hz:=positiveZeta_lower (s:=1+boundaryEta) (by norm_num [boundaryEta])
  have hp : 0<height := by norm_num [height]
  have hpow : 0<height^(1+boundaryEta) := rpow_pos_of_pos hp _
  have hpre : 1 ≤ 1+2/((1503/500)*positiveZeta (1+boundaryEta)*height^(1+boundaryEta)) := by
    have hh : 0 ≤ 2/((1503/500)*positiveZeta (1+boundaryEta)*height^(1+boundaryEta)) := by positivity
    linarith
  have hs : 1 ≤ ((1503/500:ℝ)*positiveZeta (1+boundaryEta))^2 := by nlinarith
  unfold sourceBSeven
  exact hs.trans (le_mul_of_one_le_left (sq_nonneg _) hpre)

theorem beight_ge_one : 1 ≤ sourceBEight := by
  unfold sourceBEight
  apply (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 1) (by positivity)).mpr
  norm_num [boundaryEta,height]

theorem source_cseven_nonnegative : 0 ≤ sourceCSeven eulerMascheroniConstant := by
  have hg0 : 0 ≤ eulerMascheroniConstant := by linarith [one_half_lt_eulerMascheroniConstant]
  have hg1:=euler_gamma_le_one
  have hlog2 : 0<log (2:ℝ) := log_pos (by norm_num)
  have hlogH : 0<log height := log_pos (by norm_num [height])
  have hq : 0<boundaryEta := by norm_num [boundaryEta]
  have hb0:=bsix_pos (X:=1000000000) (by norm_num) hq hg0
  have hb:=bsix_gamma_le (X:=1000000000) (by norm_num) hq hg1
  have hbu : sourceBSix 1000000000 boundaryEta 1 ≤ 3/4 := by simpa [boundaryEta] using eta_bsix_upper
  have hbval : (sourceBSix 1000000000 boundaryEta eulerMascheroniConstant)^2 ≤ 9/16 := by nlinarith
  have hbLog : log (1-(sourceBSix 1000000000 boundaryEta eulerMascheroniConstant)^2) ≤ 0 := by
    apply log_nonpos (by nlinarith) (by nlinarith [sq_nonneg (sourceBSix 1000000000 boundaryEta eulerMascheroniConstant)])
  have hlogs : 0 ≤ log sourceBSeven+log sourceBFive-
      2*log (1-(sourceBSix 1000000000 boundaryEta eulerMascheroniConstant)^2) := by
    have h5:=log_nonneg bfive_ge_one
    have h7:=log_nonneg bseven_ge_one
    linarith
  have hH : 0<height := by norm_num [height]
  have hpiH : 2*Real.pi ≤ height := by
    have hh : (8:ℝ) ≤ height := by norm_num [height]
    nlinarith [Real.pi_lt_four]
  have hr : 1/height ≤ sourceBEight/(2*Real.pi) := by
    apply (div_le_div_iff₀ hH (by positivity : 0<2*Real.pi)).mpr
    have hh:=mul_le_mul_of_nonneg_left beight_ge_one hH.le
    nlinarith
  have hrlog : -log height ≤ log (sourceBEight/(2*Real.pi)) := by
    have hh:=log_le_log (by positivity : 0<1/height) hr
    simpa only [one_div,log_inv] using hh
  have hfactor : 0 ≤ 2*(1+2*boundaryEta)/log 2 := by positivity [show (0:ℝ)<boundaryEta by norm_num [boundaryEta]]
  have hneg:=mul_le_mul_of_nonneg_left hrlog hfactor
  have hpos:=mul_nonneg (show 0 ≤ Real.pi/log 2 by positivity) hlogs
  have hB : -(2*(1+2*boundaryEta)/log 2)*log height ≤ sourceBNine eulerMascheroniConstant := by
    unfold sourceBNine
    nlinarith [Real.pi_pos]
  have hdiv:=div_le_div_of_nonneg_right hB hlogH.le
  have hcancel : (-(2*(1+2*boundaryEta)/log 2)*log height)/log height=
      -(2*(1+2*boundaryEta)/log 2) := by field_simp
  rw [hcancel] at hdiv
  unfold sourceCSeven
  have hmain : 0 ≤ (2*(1+2*boundaryEta)+2*Real.pi*(1+boundaryEta))/log 2-
      2*(1+2*boundaryEta)/log 2 := by
    rw [←sub_div]
    apply div_nonneg _ hlog2.le
    have he : 0<boundaryEta := by norm_num [boundaryEta]
    nlinarith [Real.pi_pos,mul_pos Real.pi_pos he]
  linarith

theorem source_ceight_nonnegative : 0 ≤ sourceCEight eulerMascheroniConstant := by
  have hg0 : 0 ≤ eulerMascheroniConstant := by linarith [one_half_lt_eulerMascheroniConstant]
  have hq : 0<boundaryMu-1 := by norm_num [boundaryMu]
  have hb0:=bsix_pos (X:=height) (by norm_num [height]) hq hg0
  have hb:=bsix_gamma_le (X:=height) (by norm_num [height]) hq euler_gamma_le_one
  have hbu : sourceBSix height (boundaryMu-1) 1 ≤ 1/4 := by
    rw [show boundaryMu-1=(237/1000:ℝ) by norm_num [boundaryMu]]
    exact mu_bsix_upper
  have hs : (sourceBSix height (boundaryMu-1) eulerMascheroniConstant)^2 ≤ 1/16 := by nlinarith
  have hl : log (1-(sourceBSix height (boundaryMu-1) eulerMascheroniConstant)^2) ≤ 0 := by
    apply log_nonpos (by nlinarith) (by nlinarith [sq_nonneg (sourceBSix height (boundaryMu-1) eulerMascheroniConstant)])
  have ht : 0 ≤ sourceBTen eulerMascheroniConstant := by
    unfold sourceBTen
    exact div_nonneg (by linarith) (sq_nonneg _)
  exact mul_nonneg ht ceight_base_nonneg

#print axioms source_cseven_nonnegative
#print axioms source_ceight_nonnegative
end WinnerOriginalScalars
