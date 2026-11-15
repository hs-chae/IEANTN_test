import SynergyAnalytic.ActualMoment
import SynergyAnalytic.ExactCount
import WinnerDensityA.HeightPrimary
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerBetaA.ActualObject
open WinnerBetaA.HeightSource WinnerNewHeightSource
set_option maxHeartbeats 0

noncomputable def continuousLeftCap (j0 j1 j2 T : ℝ) : ℝ :=
  2*Real.exp ((601/5000:ℝ)/(2*T^2))*
    errorBudget T (Real.log T) ((1461/1000:ℝ)/zetaScale T)
      (1/10000) (7/10000) (meanOne T) (meanTwo T) j0 j1 j2
noncomputable def continuousRightCap (delta T : ℝ) : ℝ :=
  rightV (289/500) delta T*Real.log T^2
noncomputable def continuousDensity (d delta j0 j1 j2 sigma T : ℝ) : ℝ :=
  sourceSmoothingR*Real.exp (2*WinnerNewHeightSource.alpha)*Real.log T/(2*Real.pi*d)*
    stripProduct (continuousLeftCap j0 j1 j2 T) (continuousRightCap delta T)
      sigma (rightLine delta T) (d/Real.log T)+6*Real.log T^2

/-- Elementary source-height geometry, with no native numerical leaf. -/
theorem source_log_ge28 {T : ℝ} (hT : height ≤ T) : 28 ≤ Real.log T := by
  have hTp : 0<T := lt_of_lt_of_le (by norm_num [height]) hT
  apply Real.exp_le_exp.mp
  rw [Real.exp_log hTp]
  calc
    Real.exp 28 = (Real.exp 1)^28 := by rw [←Real.exp_nat_mul];norm_num
    _ ≤ (11/4:ℝ)^28 := pow_le_pow_left₀ (Real.exp_pos _).le
      (Real.exp_one_lt_d9.le.trans (by norm_num)) 28
    _ ≤ height := by norm_num [height]
    _ ≤ T := hT

/-- The three fixed universal numerical residuals control the actual left
moment at EVERY height, not only at a list of chosen anchors. -/
theorem continuous_left_from_source {d delta j0 j1 j2 T : ℝ}
    (h : PrimaryInputs d delta) (hcaps : UniversalBasisCaps j0 j1 j2)
    (hT : height ≤ T) : sourceMoment T (1/2) ≤ continuousLeftCap j0 j1 j2 T := by
  have hT1 : 1 < T := lt_of_lt_of_le (by norm_num [height]) hT
  have hlog : 14 ≤ Real.log T := by linarith [source_log_ge28 hT]
  exact actual_source_moment_from_basis hT1 hlog le_rfl le_rfl (by norm_num) (by norm_num)
    (meanOne_nonneg hT1) (meanTwo_nonneg hT1) hcaps h.lowZeta h.reversZeta
    (h.mollifierMeanSquare T hT) (h.sourceSmoothing T hT)

theorem continuous_right_from_source {d delta T : ℝ}
    (h : PrimaryInputs d delta) (hd : 0 < delta) (hT : height ≤ T) :
    sourceMoment T (rightLine delta T) ≤ continuousRightCap delta T := by
  have hT1 : 1<T := lt_of_lt_of_le (by norm_num [height]) hT
  have hg := WinnerEulerGamma.euler_gamma_upper
  have hv := (rightVExact_le (by linarith : eulerMascheroniConstant≤1) hd hT1).trans
    (rightV_uniform_to hg (by norm_num : (0:ℝ)≤289/500) hd hT1 le_rfl)
  exact (h.sourceRightMoment T hT).trans (mul_le_mul_of_nonneg_right hv (sq_nonneg _))

/-- Exact finite-T interpolation and the original regular-contour count.
This avoids the older K/B uniformization and keeps the true T-dependence. -/
theorem continuous_count_regular {d delta j0 j1 j2 sigma T : ℝ}
    (h : PrimaryInputs d delta) (hcaps : UniversalBasisCaps j0 j1 j2)
    (hd : (34/100:ℝ) ≤ d) (hdmax : d ≤ 2/5) (hdelta : 0 < delta)
    (hs : (3/4:ℝ) ≤ sigma) (hs' : sigma ≤ 7/8) (hT : height ≤ T)
    (hRegular : IEANTN.zetaN' sigma T ≤
      ((T-WinnerNewHeightSource.Hstar)*Real.log (1+sourceFdiff d sigma T/(T-WinnerNewHeightSource.Hstar))+
        (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted d sigma T)+
          sourceCEight eulerMascheroniConstant/2)*Real.log T)/
          (2*Real.pi*(sigma-shifted d sigma T))) :
    IEANTN.zetaN' sigma T ≤ continuousDensity d delta j0 j1 j2 sigma T := by
  have hnew := h.toNewInputs (by linarith : 0<d)
  have hT1 : 1<T := lt_of_lt_of_le (by norm_num [height]) hT
  have hL : 28 ≤ Real.log T := source_log_ge28 hT
  have hLp : 0<Real.log T := by linarith
  have hdp : 0<d := by linarith
  have hdr : d/Real.log T ≤ (1/70:ℝ) := by
    apply (div_le_iff₀ hLp).mpr
    nlinarith
  have hshift : sigma-d/Real.log T ≤ 7/8 := by have ht:=div_pos hdp hLp;linarith
  have hLeft : (1/2:ℝ) ≤ sigma-d/Real.log T := by linarith
  have hdl : 0<delta/Real.log T := div_pos hdelta hLp
  have hRight : sigma-d/Real.log T ≤ rightLine delta T := by unfold rightLine;linarith
  have hWidth : (1/2:ℝ) < rightLine delta T := by unfold rightLine;linarith
  have hHeight : WinnerNewHeightSource.Hstar < T := by unfold WinnerNewHeightSource.Hstar;linarith
  have hMu : 0 ≤ (1237/1000:ℝ)-shifted d sigma T := by unfold shifted;linarith
  have hReg : IEANTN.zetaN' sigma T ≤
      ((T-WinnerNewHeightSource.Hstar)*Real.log (1+sourceFdiff d sigma T/(T-WinnerNewHeightSource.Hstar))+
        (20*((1237/1000:ℝ)-shifted d sigma T)+1/2)*Real.log T)/
          (2*Real.pi*(sigma-shifted d sigma T)) := by
    apply hRegular.trans
    apply div_le_div_of_nonneg_right _
      (mul_nonneg (by positivity) (by unfold shifted;have ht:=div_pos hdp hLp;linarith))
    have h7 := mul_le_mul_of_nonneg_right source_cseven_upper hMu
    have h8 := source_ceight_upper
    have hb : sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted d sigma T)+
        sourceCEight eulerMascheroniConstant/2 ≤ 20*((1237/1000:ℝ)-shifted d sigma T)+1/2 := by linarith
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hLp.le)
  have hc := exact_count_from_source_moments hT1 hdp hHeight
    (sourceOmega_pos d sigma T) hLeft hRight hWidth (actual_Fdiff_nonneg hdp hs' hT)
    (WinnerSourceContext.sourceMoment_nonneg T (1/2))
    (WinnerSourceContext.sourceMoment_nonneg T (rightLine delta T)) hReg
    (h.sourceUnsmoothing sigma T hs hs' hT) (h.sourceInterpolation sigma T hs hs' hT)
    (continuous_left_from_source h hcaps hT) (continuous_right_from_source h hdelta hT)
    (sourceOmega_reciprocal d sigma T)
  have hb := boundary_coefficient_le_six_extended hs hd hdmax hL
    (by norm_num : (1237/1000:ℝ)≤5/4) (by norm_num : (0:ℝ)≤20)
    (by norm_num : (20:ℝ)≤20) (by norm_num : (1:ℝ)≤1)
  apply hc.trans
  unfold continuousDensity
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (sq_nonneg _))

#print axioms continuous_left_from_source
#print axioms continuous_right_from_source
#print axioms continuous_count_regular
end SynergyAnalytic
