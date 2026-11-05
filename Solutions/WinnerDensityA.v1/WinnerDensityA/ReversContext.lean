/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.SourceContext
import WinnerBetaA.ReversMoment
import ReversSourceLink

namespace WinnerSourceContext
open Real Set MeasureTheory
open WinnerBetaA.ActualObject WinnerOriginalScalars WinnerDensitySource
set_option maxHeartbeats 0

/-- Same seven shared original-source inputs, with the high-height zeta field
replaced by the separately sourced Revers Theorem1.1(a).  No HPY hypothesis
or desired improved moment/density bound is retained as an input. -/
structure ReversInputs : Prop where
  /-- Low-height estimate in KLN Lemma3.2 proof, printed p6, citing Hiary. -/
  lowZeta : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ)
  /-- Revers arXiv2602.05614v1 Theorem1.1(a), on its actual domain. -/
  reversZeta : ∀ u : ℝ, 3 ≤ u →
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (611/1000)*u^((1:ℝ)/6)*log u
  /-- Original KLN Lemma4.1 Eq4.2. -/
  mollifierMeanSquare : ∀ T : ℝ, height ≤ T → ∀ t > 0,
    (∫ u in (0:ℝ)..t, ‖mollifier T (vertical (1/2) u)‖^2) ≤
      (sourceM1*t+sourceM2*T)*log T
  /-- Original KLN Lemma4.5 Eq4.13, weight beta=2. -/
  sourceSmoothing : ∀ T : ℝ, height ≤ T → sourceMoment T (1/2) ≤
    (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫ x in Ioi 0, WinnerBetaA.Minkowski.gaussianWeight x*scaledCriticalF T x)
  /-- Original KLN Lemma4.7, Eqs4.19/4.20 (printed pp12–13), retaining the independently defined V(T). -/
  sourceRightMoment : ∀ T : ℝ, height ≤ T →
    sourceMoment T (rightLine T) ≤ sourceRightV eulerMascheroniConstant T*(log T)^2
  /-- KLN2.3+2.9 and Lemma4.14 first display, with original4.12/4.13
  boundary terms and the FKS2.7 proof's C8/2 improvement. The relation is required only at nonexceptional heights, with a countable
  set allowed to depend on sigma. Universal height validity is proved only
  after the new continuous polynomial profile has been derived. -/
  sourceCount : IEANTN.RiemannHypothesisUpTo height → ∀ sigma : ℝ,
    (3/4:ℝ) ≤ sigma → sigma ≤ 7/8 → ∃ E : Set ℝ, E.Countable ∧
      ∀ T : ℝ, height ≤ T → T ∉ E →
    IEANTN.zetaN' sigma T ≤
      ((T-Hstar)*log (1+sourceFdiff sigma T/(T-Hstar))+
        (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted sigma T)+
          sourceCEight eulerMascheroniConstant/2)*log T)/
        (2*Real.pi*(sigma-shifted sigma T))
  /-- KLN Lemma4.9 proof before substitution, with exact Eq3.19 omega2. -/
  sourceUnsmoothing : ∀ sigma T : ℝ, (3/4:ℝ) ≤ sigma → sigma ≤ 7/8 → height ≤ T →
    sourceFdiff sigma T ≤ sourceMoment T (shifted sigma T)/(2*sourceOmega sigma T^2)
  /-- KLN Lemma4.4 Eq4.12 on its admissible strip, before every U relaxation. -/
  sourceInterpolation : ∀ sigma T : ℝ, (3/4:ℝ) ≤ sigma → sigma ≤ 7/8 → height ≤ T →
    sourceMoment T (shifted sigma T) ≤
      sourceMoment T (1/2)^((rightLine T-shifted sigma T)/(rightLine T-1/2))*
      sourceMoment T (rightLine T)^((shifted sigma T-1/2)/(rightLine T-1/2))

/-- This input package can also supply the unchanged original HPY interface. -/
theorem ReversInputs.toOriginalInputs (h : ReversInputs) : OriginalInputs :=
  ⟨h.lowZeta,WinnerBetaA.ReversMoment.revers_supplies_hpy h.reversZeta,
    h.mollifierMeanSquare,h.sourceSmoothing,h.sourceRightMoment,
    h.sourceCount,h.sourceUnsmoothing,h.sourceInterpolation⟩

/-- Revers supplies the input improvement; the independently proved new
Minkowski/Gaussian mechanism supplies U=1.286. Their effects remain distinct. -/
private theorem actual_count_revers_from_original_sources_at_regular_height (h : ReversInputs)
    {sigma T : ℝ} (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T)
    (hRegularCount :
    IEANTN.zetaN' sigma T ≤
      ((T-Hstar)*log (1+sourceFdiff sigma T/(T-Hstar))+
        (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted sigma T)+
          sourceCEight eulerMascheroniConstant/2)*log T)/
        (2*Real.pi*(sigma-shifted sigma T)) ) :
    IEANTN.zetaN' sigma T ≤
      ((15/2:ℝ)*exp (-(547/100:ℝ)*(7/8-sigma)))*
        T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  have hH : 0 < height := by norm_num [height]
  have hTp : 0 < T := hH.trans_le hT
  have hL : 28 ≤ log T := source_log_height_uniform hT
  have hLp : 0 < log T := by linarith
  have hT1 : 1 < T := (log_pos_iff hTp.le).mp hLp
  have hHeight : Hstar < T := by unfold Hstar;linarith
  have hGap : 0 < sigma-shifted sigma T := by
    unfold shifted
    have := div_pos (by norm_num [d] : 0<d) hLp
    linarith
  have hMu : 0 ≤ (1237/1000:ℝ)-shifted sigma T := by
    unfold shifted
    have := div_nonneg (by norm_num [d] : 0≤d) hLp.le
    linarith
  have hSourceCount : IEANTN.zetaN' sigma T ≤
      ((T-Hstar)*log (1+sourceFdiff sigma T/(T-Hstar))+
        (20*((1237/1000:ℝ)-shifted sigma T)+(1:ℝ)/2)*log T)/
        (2*Real.pi*(sigma-shifted sigma T)) := by
    apply hRegularCount.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hSeven := mul_le_mul_of_nonneg_right source_cseven_upper hMu
    have hEight := source_ceight_upper
    have hb : sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted sigma T)+
          sourceCEight eulerMascheroniConstant/2 ≤
        20*((1237/1000:ℝ)-shifted sigma T)+(1:ℝ)/2 := by linarith
    have hbL := mul_le_mul_of_nonneg_right hb hLp.le
    linarith
  have hLeft := WinnerBetaA.ReversMoment.actual_left_U1286_from_primary_inputs hT h.lowZeta h.reversZeta
    (h.mollifierMeanSquare T hT) (h.sourceSmoothing T hT)
  have hRight := right_moment_upper (Mright:=fun u => sourceMoment u (rightLine u)) hT
    (h.sourceRightMoment T hT)
  have hPoly := count_poly_of_source_moments hs hs'
    (d:=d) (delta:=delta) (alpha:=alpha) (R:=sourceSmoothingR)
    (by norm_num [d]) (by norm_num [d]) hT1 hL (by norm_num [delta])
    (by norm_num : (0:ℝ)<643/500) (by norm_num : (0:ℝ)<17/2)
    (by unfold sourceSmoothingR;positivity)
    (by norm_num : (1237/1000:ℝ)≤5/4) (by norm_num : (0:ℝ)≤20)
    (by norm_num : (20:ℝ)≤20) (by norm_num : (1:ℝ)≤1)
    hHeight (sourceOmega_pos sigma T) (actual_Fdiff_nonneg hs' hT)
    (sourceMoment_nonneg T (1/2)) (sourceMoment_nonneg T (rightLine T))
    hSourceCount (h.sourceUnsmoothing sigma T hs hs' hT)
    (h.sourceInterpolation sigma T hs hs' hT) hLeft hRight (sourceOmega_reciprocal sigma T)
  have hCap := densityCoefficient_model_cap (d:=d) (delta:=delta) (alpha:=alpha)
    (U:=643/500) (V:=17/2) (R:=sourceSmoothingR) (beta:=7/8)
    (by norm_num) (by norm_num) (by norm_num [d]) (by unfold sourceSmoothingR;positivity)
    hs' WinnerOriginalScalars.Revers.actual_coefficient_upper WinnerOriginalScalars.Revers.actual_slope_lower
  have hm := mul_le_mul_of_nonneg_right hCap
    (show 0≤T^(8*(1-sigma)/3)*log T^(5-2*sigma) by positivity)
  apply hPoly.trans
  nlinarith


/-- The newly derived polynomial majorant is continuous in height.  Extend
from the source's nonexceptional heights by actual count monotonicity; no
continuity of the raw F expression or floor-dependent mollifier is assumed. -/
theorem actual_count_revers_from_original_sources (h : ReversInputs)
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    {sigma T : ℝ} (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T) :
    IEANTN.zetaN' sigma T ≤
      ((15/2:ℝ)*exp (-(547/100:ℝ)*(7/8-sigma)))*
        T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  obtain ⟨E,hE,hRegular⟩ := h.sourceCount hRH sigma hs hs'
  have hTp : 0 < T := lt_of_lt_of_le (by norm_num [height]) hT
  have hLp : 0 < log T := lt_of_lt_of_le (by norm_num : (0:ℝ)<28)
    (source_log_height_uniform hT)
  have hQ : ContinuousAt (fun u : ℝ =>
      ((15/2:ℝ)*exp (-(547/100:ℝ)*(7/8-sigma)))*
        u^(8*(1-sigma)/3)*log u^(5-2*sigma)+6*log u^(2:ℕ)) T := by
    have hp : ContinuousAt (fun u : ℝ => u^(8*(1-sigma)/3)) T :=
      continuousAt_id.rpow_const (Or.inl hTp.ne')
    have hl : ContinuousAt (fun u : ℝ => log u) T := continuousAt_log hTp.ne'
    have hq : ContinuousAt (fun u : ℝ => log u^(5-2*sigma)) T :=
      hl.rpow_const (Or.inl hLp.ne')
    exact ((continuousAt_const.mul hp).mul hq).add ((hl.pow 2).const_mul 6)
  apply WinnerExceptionalDensity.zetaN_extend hE hT hQ
  intro u hu hnot
  exact actual_count_revers_from_original_sources_at_regular_height h hs hs' hu (hRegular u hu hnot)

#print axioms actual_count_revers_from_original_sources
#check actual_count_revers_from_original_sources
end WinnerSourceContext
