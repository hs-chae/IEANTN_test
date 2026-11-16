import SynergyAnalytic.UniformBasis
import WinnerDensityA.Moment
namespace SynergyAnalytic
open Real Set MeasureTheory WinnerOriginalScalars WinnerBetaA.ActualObject
open WinnerBetaA.HeightSource WinnerNewHeightSource WinnerDensitySource
set_option maxHeartbeats 0

/-- A coarse tail density comes from the same actual source moment. The left
moment argument is supplied by actual_left_uniform_basis in the final wrapper. -/
theorem coarse_count_regular {d delta A T U V k sigma:ℝ}
    (h:PrimaryInputs d delta) (hd:(34/100:ℝ) ≤ d) (hdmax:d ≤ 2/5) (hdelta:0<delta)
    (hAH:height ≤  A) (hAT:A ≤  T) (hU:0<U) (hV:0<V)
    (hLeftRaw:sourceMoment T (1/2) ≤ U*T^((4:ℝ)/3)*Real.log T^3)
    (hRight:WinnerBetaA.HeightSource.rightV (289/500) delta A ≤  V)
    (hK:densityCoefficient (7/8) d delta WinnerNewHeightSource.alpha U V sourceSmoothingR ≤  k)
    (hB:(0:ℝ) ≤ densitySlope delta U V) (hs:(3/4:ℝ) ≤  sigma) (hs':sigma ≤ 7/8)
    (hRegular:IEANTN.zetaN' sigma T ≤ 
      ((T-WinnerNewHeightSource.Hstar)*Real.log (1+sourceFdiff d sigma T/(T-WinnerNewHeightSource.Hstar))+
        (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted d sigma T)+
          sourceCEight eulerMascheroniConstant/2)*Real.log T)/(2*Real.pi*(sigma-shifted d sigma T))) :
    IEANTN.zetaN' sigma T ≤  k*T^(8*(1-sigma)/3)*Real.log T^(5-2*sigma)+6*Real.log T^2 := by
  have hTH:height ≤  T := hAH.trans hAT
  have hTp:0<T := lt_of_lt_of_le (by norm_num [height]) hTH
  have hL:28 ≤ log T := source_log_height_uniform hTH
  have hLp:0<log T := by linarith
  have hT1:1<T := (log_pos_iff hTp.le).mp hLp
  have hdp:0<d := by linarith
  have hHeight:WinnerNewHeightSource.Hstar<T := by unfold WinnerNewHeightSource.Hstar;linarith
  have hGap:0<sigma-shifted d sigma T := by unfold shifted;have hh:=div_pos hdp hLp;linarith
  have hMu:0 ≤ (1237/1000:ℝ)-shifted d sigma T := by
    unfold shifted
    have hh:=div_nonneg hdp.le hLp.le
    linarith
  have hCount:IEANTN.zetaN' sigma T ≤ 
      ((T-Hstar)*log (1+sourceFdiff d sigma T/(T-Hstar))+
        (20*((1237/1000:ℝ)-shifted d sigma T)+(1:ℝ)/2)*log T)/
        (2*Real.pi*(sigma-shifted d sigma T)) := by
    apply hRegular.trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hSeven:=mul_le_mul_of_nonneg_right source_cseven_upper hMu
    have hEight:=source_ceight_upper
    have hb:sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted d sigma T)+
        sourceCEight eulerMascheroniConstant/2 ≤ 20*((1237/1000:ℝ)-shifted d sigma T)+1/2 := by linarith
    have hh:=mul_le_mul_of_nonneg_right hb hLp.le
    linarith
  have hLeft := hLeftRaw
  have hRightM:=actual_right_from_certificate (h.toNewInputs hdp) hdelta hAH hAT hRight
  have hPoly:=count_poly_of_source_moments_extended hs hs' hd hdmax hT1 hL hdelta.le hU hV
    (by unfold sourceSmoothingR;positivity)
    (by norm_num : (1237/1000:ℝ) ≤ 5/4) (by norm_num : (0:ℝ) ≤ 20)
    (by norm_num : (20:ℝ) ≤ 20) (by norm_num : (1:ℝ) ≤ 1)
    hHeight (sourceOmega_pos d sigma T) (actual_Fdiff_nonneg hdp hs' hTH)
    (WinnerSourceContext.sourceMoment_nonneg T (1/2))
    (WinnerSourceContext.sourceMoment_nonneg T (rightLine delta T))
    hCount (h.sourceUnsmoothing sigma T hs hs' hTH) (h.sourceInterpolation sigma T hs hs' hTH)
    hLeft hRightM (sourceOmega_reciprocal d sigma T)
  have hCap:=densityCoefficient_model_cap (B:=0) hU hV hdp
    (show 0 ≤ sourceSmoothingR by unfold sourceSmoothingR;positivity) hs' hK hB
  have hm:=mul_le_mul_of_nonneg_right hCap
    (show 0 ≤  T^(8*(1-sigma)/3)*log T^(5-2*sigma) by positivity)
  norm_num only [neg_zero,zero_mul,Real.exp_zero,mul_one] at hm
  exact hPoly.trans (by nlinarith [hm])


#print axioms coarse_count_regular
end SynergyAnalytic
