/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.HeightCertified
import WinnerDensityA.ActualLowerContour
namespace WinnerNewHeightSource
open Real Set MeasureTheory
open WinnerOriginalScalars WinnerBetaA.ActualObject WinnerBetaA.HeightSource WinnerLowerContour
set_option maxHeartbeats 0

/-- The original regular rectangle contract has a count difference and no
selected lower-contour or chosen density/moment conclusion. -/
structure PrimaryInputs (d delta:ℝ) : Prop where
  lowZeta : ∀u:ℝ,0≤u→u≤3→‖riemannZeta (vertical (1/2) u)‖≤(1461/1000:ℝ)
  reversZeta : ∀u:ℝ,3≤u→‖riemannZeta (vertical (1/2) u)‖≤(611/1000)*u^((1:ℝ)/6)*log u
  mollifierMeanSquare : ∀T:ℝ,height≤T→∀t>0,
    (∫u in (0:ℝ)..t,‖mollifier T (vertical (1/2) u)‖^2)≤(meanOne T*t+meanTwo T*T)*log T
  sourceSmoothing : ∀T:ℝ,height≤T→sourceMoment T (1/2)≤
    (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫x in Ioi 0,WinnerBetaA.Minkowski.gaussianWeight x*scaledCriticalF T x)
  sourceRightMoment : ∀T:ℝ,height≤T→sourceMoment T (rightLine delta T)≤
    rightVExact eulerMascheroniConstant delta T*log T^(2:ℕ)
  sourceRectangle : ∀sigma:ℝ,(3/4:ℝ)≤sigma→sigma≤7/8→
    ∃Etop:Set ℝ,Etop.Countable ∧ ∀T:ℝ,height≤T→T∉Etop→
      ∃Elower:Set ℝ,Elower.Countable ∧ ∀h:ℝ,height-1<h→h<height→h∉Elower→
        IEANTN.zetaN' sigma T-IEANTN.zetaN' sigma h≤
          rawRectangleBound T sigma (sigma-d/log T) (1237/1000)
            (cSevenAt eulerMascheroniConstant h) (sourceCEight eulerMascheroniConstant) T h
  sourceUnsmoothing : ∀sigma T:ℝ,(3/4:ℝ)≤sigma→sigma≤7/8→height≤T→
    sourceFdiff d sigma T≤sourceMoment T (shifted d sigma T)/(2*sourceOmega d sigma T^2)
  sourceInterpolation : ∀sigma T:ℝ,(3/4:ℝ)≤sigma→sigma≤7/8→height≤T→
    sourceMoment T (shifted d sigma T)≤
      sourceMoment T (1/2)^((rightLine delta T-shifted d sigma T)/(rightLine delta T-1/2))*
      sourceMoment T (rightLine delta T)^((shifted d sigma T-1/2)/(rightLine delta T-1/2))

theorem selected_lower_contour_param {d:ℝ} (hd:0<d)
    (hRH:IEANTN.RiemannHypothesisUpTo height) {sigma T:ℝ}
    (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:height≤T)
    (hRect:∃E:Set ℝ,E.Countable ∧ ∀h:ℝ,height-1<h→h<height→h∉E→
      IEANTN.zetaN' sigma T-IEANTN.zetaN' sigma h≤
        rawRectangleBound T sigma (sigma-d/log T) (1237/1000)
          (cSevenAt eulerMascheroniConstant h) (sourceCEight eulerMascheroniConstant) T h) :
    IEANTN.zetaN' sigma T≤rawRectangleBound T sigma (sigma-d/log T) (1237/1000)
      (sourceCSeven eulerMascheroniConstant) (sourceCEight eulerMascheroniConstant) T (height-1) := by
  obtain ⟨E,hE,hsource⟩:=hRect
  have hT1:1<T:=lt_of_lt_of_le (by norm_num [height]) hT
  have hlog:0<log T:=log_pos hT1
  have hq:0<d/log T:=div_pos hd hlog
  have hsne:sigma-d/log T≠1:=by linarith
  have hgap:sigma-d/log T<sigma:=by linarith
  have hmu:sigma-d/log T≤(1237/1000:ℝ):=by linarith
  apply limit_from_regular_lower_edges (H0:=height) (E:=E) (by linarith) hE
    (raw_lower_continuous hsne (by linarith))
  intro u hu hu' hnot
  have hc:=hsource u hu hu' hnot
  rw [actual_low_count_zero hRH hs hu'.le,sub_zero] at hc
  apply hc.trans
  apply raw_C7_mono hgap hmu hT1.le
  rw [←cSevenAt_selected]
  exact cSevenAt_antitone eulerMascheroniConstant (by norm_num [height]) hu.le

/-- Selected lower edges and low-count removal are formally derived. -/
theorem PrimaryInputs.toNewInputs {d delta:ℝ} (h:PrimaryInputs d delta) (hd:0<d) :
    NewInputs d delta where
  lowZeta:=h.lowZeta
  reversZeta:=h.reversZeta
  mollifierMeanSquare:=h.mollifierMeanSquare
  sourceSmoothing:=h.sourceSmoothing
  sourceRightMoment:=h.sourceRightMoment
  sourceUnsmoothing:=h.sourceUnsmoothing
  sourceInterpolation:=h.sourceInterpolation
  sourceCount:=by
    intro hRH sigma hs hs'
    obtain ⟨E,hE,hTop⟩:=h.sourceRectangle sigma hs hs'
    refine ⟨E,hE,?_⟩
    intro T hT hnot
    have hb:=selected_lower_contour_param hd hRH hs hs' hT (hTop T hT hnot)
    simpa only [rawRectangleBound,Hstar,sourceFdiff,shifted] using hb

/-- Final actual four-profile count API from the lowest regular-contour
source package. Finite RH stays at3e12, not at any larger profile height. -/
theorem primary_profile_count (h:PrimaryInputs (3681/10000) (3599/10000))
    (hRH:IEANTN.RiemannHypothesisUpTo height) (j:Fin 4)
    {sigma T:ℝ} (hs:(3/4:ℝ)≤sigma) (hs':sigma≤7/8) (hT:WinnerHeightProfiles.anchor j≤T) :
    IEANTN.zetaN' sigma T≤((WinnerHeightProfiles.row j).K:ℝ)*
      exp ((54281/10000:ℝ)*(sigma-7/8))*T^(8*(1-sigma)/3)*log T^(5-2*sigma)+6*log T^(2:ℕ) := by
  have hb:=profile_count (h.toNewInputs (by norm_num)) hRH j hs hs' hT
  simpa only [show -(54281/10000:ℝ)*(7/8-sigma)=(54281/10000:ℝ)*(sigma-7/8) by ring] using hb

#print axioms selected_lower_contour_param
#print axioms primary_profile_count
#check primary_profile_count
end WinnerNewHeightSource
