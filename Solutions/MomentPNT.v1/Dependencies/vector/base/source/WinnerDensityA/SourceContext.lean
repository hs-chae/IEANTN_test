/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import SourceDensityPoly
import ExceptionalDensity
import WinnerBetaA.ActualObject
import WinnerBetaA.RawSource
import OriginalRightMoment
import OriginalSourceLink
import OriginalBoundaryScalars
namespace WinnerSourceContext
open Real Set MeasureTheory
open WinnerBetaA.ActualObject WinnerOriginalScalars WinnerDensitySource
set_option maxHeartbeats 0

noncomputable def d : ℝ := 851/2500
noncomputable def delta : ℝ := 3119/10000
noncomputable def alpha : ℝ := 601/5000
noncomputable def Hstar : ℝ := height-1
noncomputable def shifted (sigma T : ℝ) : ℝ := sigma-d/log T
noncomputable def rightLine (T : ℝ) : ℝ := 1+delta/log T
noncomputable def sourceOmega (sigma T : ℝ) : ℝ :=
  (1-1/Hstar)*exp (alpha*((shifted sigma T)/T)^2-alpha)
noncomputable def sourceFdiff (sigma T : ℝ) : ℝ :=
  cumulativeSquare T (shifted sigma T) T-cumulativeSquare T (shifted sigma T) Hstar

/-- Regularity of the actual mollified zeta function on every pole-free vertical line. -/
theorem vertical_error_continuous {sigma : ℝ} (hs : sigma ≠ 1) (X : ℝ) :
    Continuous (fun t : ℝ => mollifiedError X (vertical sigma t)) := by
  have hζ : Continuous (fun t : ℝ => riemannZeta (vertical sigma t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : vertical sigma t ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [vertical,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,
        add_zero,Complex.one_re] at hr
      exact hs hr
    exact (differentiableAt_riemannZeta hne).continuousAt.comp (vertical_continuous sigma).continuousAt
  exact (hζ.mul ((mollifier_continuous X).comp (vertical_continuous sigma))).sub continuous_const

theorem actual_Fdiff_nonneg {sigma T : ℝ} (hs : sigma ≤ 7/8) (hT : height ≤ T) :
    0 ≤ sourceFdiff sigma T := by
  have hH : 0 < height := by norm_num [height]
  have hTp : 0 < T := hH.trans_le hT
  have hL : 0 < log T := lt_of_lt_of_le (by linarith [source_log_lower]) (log_le_log hH hT)
  have hsne : shifted sigma T ≠ 1 := by
    have hd : 0 < d/log T := div_pos (by norm_num [d]) hL
    unfold shifted
    linarith
  have hc : Continuous (fun u : ℝ => ‖mollifiedError T (vertical (shifted sigma T) u)‖^2) :=
    (vertical_error_continuous hsne T).norm.pow 2
  have hi : (∫ u in (0:ℝ)..Hstar, ‖mollifiedError T (vertical (shifted sigma T) u)‖^2)+
      (∫ u in Hstar..T, ‖mollifiedError T (vertical (shifted sigma T) u)‖^2) =
      (∫ u in (0:ℝ)..T, ‖mollifiedError T (vertical (shifted sigma T) u)‖^2) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 Hstar) (hc.intervalIntegrable Hstar T)
  have hp : 0 ≤ ∫ u in Hstar..T, ‖mollifiedError T (vertical (shifted sigma T) u)‖^2 := by
    apply intervalIntegral.integral_nonneg_of_forall
    · unfold Hstar
      linarith
    · intro u
      positivity
  unfold sourceFdiff cumulativeSquare
  linarith

theorem sourceOmega_pos (sigma T : ℝ) : 0 < sourceOmega sigma T := by
  have hb : 0 < 1-1/Hstar := by norm_num [Hstar,height]
  unfold sourceOmega
  exact mul_pos hb (exp_pos _)

/-- Exact original Eq.3.19 implies its independent reciprocal smoothing allowance. -/
theorem sourceOmega_reciprocal (sigma T : ℝ) :
    1/(2*sourceOmega sigma T^2) ≤ sourceSmoothingR*exp (2*alpha) := by
  have hbase : 0 < 1-1/Hstar := by norm_num [Hstar,height]
  have ha : 0 ≤ alpha*((shifted sigma T)/T)^2 := by unfold alpha; positivity
  have he : exp (-alpha) ≤ exp (alpha*((shifted sigma T)/T)^2-alpha) :=
    exp_le_exp.mpr (by linarith)
  have ho : (1-1/Hstar)*exp (-alpha) ≤ sourceOmega sigma T := by
    exact mul_le_mul_of_nonneg_left he hbase.le
  have hl : 0 < (1-1/Hstar)*exp (-alpha) := by positivity
  have hsq : 2*((1-1/Hstar)*exp (-alpha))^2 ≤ 2*sourceOmega sigma T^2 := by
    have := sq_le_sq₀ hl.le (sourceOmega_pos sigma T).le |>.mpr ho
    linarith
  have hh := one_div_le_one_div_of_le (by positivity : 0 < 2*((1-1/Hstar)*exp (-alpha))^2) hsq
  apply hh.trans_eq
  rw [mul_pow, ← exp_nat_mul]
  rw [show (2:ℕ)*(-alpha)=-(2*alpha) by norm_num,exp_neg]
  unfold sourceSmoothingR Hstar
  field_simp
  <;> ring


/-- Independently named original primary-source facts, all on the actual
mollifier/zeta objects.  No chosen U,V,density or prime bound is a field. -/
structure OriginalInputs : Prop where
  /-- Hiary Theorem1.1 low-height estimate, cited KLN Lemma3.2 proof p6. -/
  lowZeta : ∀ u : ℝ, 0 ≤ u → u ≤ 3 →
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ)
  /-- HPY/FKS0.618 critical-line estimate, on its actual domain. -/
  hpyZeta : ∀ u : ℝ, 3 ≤ u →
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*u^((1:ℝ)/6)*log u
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

theorem sourceMoment_nonneg (T sigma : ℝ) : 0 ≤ sourceMoment T sigma := by
  unfold sourceMoment
  exact integral_nonneg (by intro t; positivity)

/-- New executed U certificate, unaltered right source, exact interpolation,
and checked coefficient/slope caps produce the actual zero-count input.
There is no improved-count, U=1.34, V=8.5, or numerical-check premise. -/
private theorem actual_count_from_original_sources_at_regular_height (h : OriginalInputs)
    {sigma T : ℝ} (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T)
    (hRegularCount :
    IEANTN.zetaN' sigma T ≤
      ((T-Hstar)*log (1+sourceFdiff sigma T/(T-Hstar))+
        (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted sigma T)+
          sourceCEight eulerMascheroniConstant/2)*log T)/
        (2*Real.pi*(sigma-shifted sigma T)) ) :
    IEANTN.zetaN' sigma T ≤
      ((759/100:ℝ)*exp (-(269/50:ℝ)*(7/8-sigma)))*
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
  have hLeft := actual_left_U134_from_primary_inputs hT h.lowZeta h.hpyZeta
    (h.mollifierMeanSquare T hT) (h.sourceSmoothing T hT)
  have hRight := right_moment_upper (Mright:=fun u => sourceMoment u (rightLine u)) hT
    (h.sourceRightMoment T hT)
  have hPoly := count_poly_of_source_moments hs hs'
    (d:=d) (delta:=delta) (alpha:=alpha) (R:=sourceSmoothingR)
    (by norm_num [d]) (by norm_num [d]) hT1 hL (by norm_num [delta])
    (by norm_num : (0:ℝ)<67/50) (by norm_num : (0:ℝ)<17/2)
    (by unfold sourceSmoothingR;positivity)
    (by norm_num : (1237/1000:ℝ)≤5/4) (by norm_num : (0:ℝ)≤20)
    (by norm_num : (20:ℝ)≤20) (by norm_num : (1:ℝ)≤1)
    hHeight (sourceOmega_pos sigma T) (actual_Fdiff_nonneg hs' hT)
    (sourceMoment_nonneg T (1/2)) (sourceMoment_nonneg T (rightLine T))
    hSourceCount (h.sourceUnsmoothing sigma T hs hs' hT)
    (h.sourceInterpolation sigma T hs hs' hT) hLeft hRight (sourceOmega_reciprocal sigma T)
  have hCap := densityCoefficient_model_cap (d:=d) (delta:=delta) (alpha:=alpha)
    (U:=67/50) (V:=17/2) (R:=sourceSmoothingR) (beta:=7/8)
    (by norm_num) (by norm_num) (by norm_num [d]) (by unfold sourceSmoothingR;positivity)
    hs' actual_coefficient_upper actual_slope_lower
  have hm := mul_le_mul_of_nonneg_right hCap
    (show 0≤T^(8*(1-sigma)/3)*log T^(5-2*sigma) by positivity)
  apply hPoly.trans
  nlinarith


/-- The newly derived polynomial majorant is continuous in height.  Extend
from the source's nonexceptional heights by actual count monotonicity; no
continuity of the raw F expression or floor-dependent mollifier is assumed. -/
theorem actual_count_from_original_sources (h : OriginalInputs)
    (hRH : IEANTN.RiemannHypothesisUpTo height)
    {sigma T : ℝ} (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T) :
    IEANTN.zetaN' sigma T ≤
      ((759/100:ℝ)*exp (-(269/50:ℝ)*(7/8-sigma)))*
        T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  obtain ⟨E,hE,hRegular⟩ := h.sourceCount hRH sigma hs hs'
  have hTp : 0 < T := lt_of_lt_of_le (by norm_num [height]) hT
  have hLp : 0 < log T := lt_of_lt_of_le (by norm_num : (0:ℝ)<28)
    (source_log_height_uniform hT)
  have hQ : ContinuousAt (fun u : ℝ =>
      ((759/100:ℝ)*exp (-(269/50:ℝ)*(7/8-sigma)))*
        u^(8*(1-sigma)/3)*log u^(5-2*sigma)+6*log u^(2:ℕ)) T := by
    have hp : ContinuousAt (fun u : ℝ => u^(8*(1-sigma)/3)) T :=
      continuousAt_id.rpow_const (Or.inl hTp.ne')
    have hl : ContinuousAt (fun u : ℝ => log u) T := continuousAt_log hTp.ne'
    have hq : ContinuousAt (fun u : ℝ => log u^(5-2*sigma)) T :=
      hl.rpow_const (Or.inl hLp.ne')
    exact ((continuousAt_const.mul hp).mul hq).add ((hl.pow 2).const_mul 6)
  apply WinnerExceptionalDensity.zetaN_extend hE hT hQ
  intro u hu hnot
  exact actual_count_from_original_sources_at_regular_height h hs hs' hu (hRegular u hu hnot)

#print axioms actual_Fdiff_nonneg
#print axioms sourceOmega_reciprocal
#print axioms actual_count_from_original_sources
end WinnerSourceContext
