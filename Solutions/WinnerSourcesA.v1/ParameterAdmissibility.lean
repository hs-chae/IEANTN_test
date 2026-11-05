/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OriginalPowerIdentities
namespace WinnerOriginalScalars
open Real LeanCert.Core
set_option maxHeartbeats 0

 theorem fixed_parameter_ranges :
    (0:ℝ)<601/5000 ∧ (0:ℝ)<3119/10000 ∧ (0:ℝ)<851/2500 ∧
    (23623/100000:ℝ)<boundaryEta ∧ boundaryEta<1/2 ∧
    (1+23623/100000:ℝ)≤boundaryMu ∧ boundaryMu≤1+boundaryEta ∧
    (1002:ℝ)≤height-1 ∧ height-1<height ∧
    (30610046000:ℝ)≤height ∧ (1000000000:ℝ)/height≤1 := by
  norm_num [height,boundaryEta,boundaryMu]

/-- Source proof smallness condition at the minimal common X, stronger than
relying on the printed approximate threshold eta0. -/
def minimalMuB6 : Expr := bSix (lit 1000000000) (lit (237/1000))
 theorem minimal_mu_bsix_upper : sourceBSix 1000000000 (237/1000) 1≤999/1000 := by
  have h := closed_upper minimalMuB6 (999/1000) (by native_decide)
  simpa [minimalMuB6,bSix_semantics] using h

 theorem actual_boundary_bsix_small :
    sourceBSix 1000000000 boundaryEta eulerMascheroniConstant<1 ∧
    sourceBSix 1000000000 (boundaryMu-1) eulerMascheroniConstant<1 ∧
    sourceBSix height (boundaryMu-1) eulerMascheroniConstant<1 := by
  have hη := bsix_gamma_le (X:=1000000000) (q:=boundaryEta) (by norm_num)
    (by norm_num [boundaryEta]) euler_gamma_le_one
  have hμ := bsix_gamma_le (X:=1000000000) (q:=boundaryMu-1) (by norm_num)
    (by norm_num [boundaryMu]) euler_gamma_le_one
  have hμH := bsix_gamma_le (X:=height) (q:=boundaryMu-1) (by norm_num [height])
    (by norm_num [boundaryMu]) euler_gamma_le_one
  have hη' : sourceBSix 1000000000 boundaryEta 1≤3/4 := by simpa [boundaryEta] using eta_bsix_upper
  have hμ' : sourceBSix 1000000000 (boundaryMu-1) 1≤999/1000 := by
    norm_num [boundaryMu]
    exact minimal_mu_bsix_upper
  have hμH' : sourceBSix height (boundaryMu-1) 1≤1/4 := by
    norm_num [boundaryMu]
    exact mu_bsix_upper
  constructor
  · linarith
  constructor <;> linarith

 theorem source_mzero_lt_two : sourceM0<2 := by
  unfold sourceM0
  have hs : sqrt (6/5:ℝ)<2 := (sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  apply (sqrt_lt (by positivity) (by norm_num)).mpr
  linarith

 theorem rectangle_lower : 2*Real.pi*sourceM0<height-1 := by
  have hm0:=source_mzero_pos
  have hm:=source_mzero_lt_two
  have hp:=Real.pi_lt_four
  have hmul : Real.pi*sourceM0<(4:ℝ)*2 := by
    calc
      _≤4*sourceM0 := mul_le_mul_of_nonneg_right hp.le hm0.le
      _<4*2 := mul_lt_mul_of_pos_left hm (by norm_num)
  norm_num [height]
  linarith

 theorem internal_delta_upper : (3119/10000:ℝ)<
    log height*(log (log height)-1)/2 := by
  have hh:=source_log_lower
  have hl : log (16:ℝ)≤log (log height) := log_le_log (by norm_num) (by linarith)
  rw [show (16:ℝ)=2^4 by norm_num,log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo : (1/2:ℝ)<log 2 := by linarith [log_two_gt_d9]
  have hloglog : 2≤log (log height) := by linarith
  nlinarith

 theorem shifted_strip_and_gap {sigma T : ℝ}
    (hs : (3/4:ℝ)≤sigma) (hs' : sigma≤7/8) (hT : height≤T) :
    (1/2:ℝ)≤sigma-(851/2500)/log T ∧ sigma-(851/2500)/log T<sigma ∧
    sigma-(851/2500)/log T≤1 ∧
    sigma-(851/2500)/log T≤1+(3119/10000)/log T ∧
    sigma-(851/2500)/log T≤boundaryMu := by
  have hl:=source_log_height_uniform hT
  have hlp : 0<log T := by linarith
  have hq0 : 0<(851/2500:ℝ)/log T := by positivity
  have hq : (851/2500:ℝ)/log T≤(851/2500)/28 := by gcongr
  have hd0 : 0<(3119/10000:ℝ)/log T := by positivity
  norm_num [boundaryMu] at ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

#print axioms fixed_parameter_ranges
#print axioms actual_boundary_bsix_small
#print axioms internal_delta_upper
#print axioms shifted_strip_and_gap
end WinnerOriginalScalars
