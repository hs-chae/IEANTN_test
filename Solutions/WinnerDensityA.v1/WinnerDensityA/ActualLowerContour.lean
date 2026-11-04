/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LowerContourLimit
import WinnerBetaA.ActualObject
namespace WinnerLowerContour
open Real Set Filter Topology MeasureTheory WinnerOriginalScalars WinnerBetaA.ActualObject
set_option maxHeartbeats 0

theorem actual_vertical_error_continuous {sigma : ℝ} (hs : sigma≠1) (X : ℝ) :
    Continuous (fun t : ℝ => mollifiedError X (vertical sigma t)) := by
  have hζ : Continuous (fun t : ℝ => riemannZeta (vertical sigma t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hne : vertical sigma t≠1 := by
      intro he
      have hr:=congrArg Complex.re he
      simp only [vertical,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
        Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,
        add_zero,Complex.one_re] at hr
      exact hs hr
    exact (differentiableAt_riemannZeta hne).continuousAt.comp (vertical_continuous sigma).continuousAt
  exact (hζ.mul ((mollifier_continuous X).comp (vertical_continuous sigma))).sub continuous_const

/-- The actual primitive, with X fixed as required when moving only a contour edge. -/
theorem actual_F_endpoint_continuous {sigma : ℝ} (hs : sigma≠1) (X : ℝ) :
    Continuous (cumulativeSquare X sigma) := by
  have hc := (actual_vertical_error_continuous hs X).norm.pow 2
  exact (intervalIntegral.differentiable_integral_of_continuous hc).continuous

 theorem actual_F_difference_nonneg {sigma h T : ℝ} (hs : sigma≠1) (X : ℝ) (hh : h≤T) :
    0≤cumulativeSquare X sigma T-cumulativeSquare X sigma h := by
  have hc := (actual_vertical_error_continuous hs X).norm.pow 2
  have ha : (∫ u in (0:ℝ)..h,‖mollifiedError X (vertical sigma u)‖^2)+
      (∫ u in h..T,‖mollifiedError X (vertical sigma u)‖^2)=
      (∫ u in (0:ℝ)..T,‖mollifiedError X (vertical sigma u)‖^2) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 h) (hc.intervalIntegrable h T)
  have hn : 0≤∫ u in h..T,‖mollifiedError X (vertical sigma u)‖^2 :=
    intervalIntegral.integral_nonneg_of_forall hh (fun u => sq_nonneg _)
  unfold cumulativeSquare
  linarith

noncomputable def rawRectangleBound (X sigma sigmap mu C7 C8 T h : ℝ) : ℝ :=
  ((T-h)*log (1+(cumulativeSquare X sigmap T-cumulativeSquare X sigmap h)/(T-h))+
    (C7*(mu-sigmap)+C8/2)*log T)/(2*Real.pi*(sigma-sigmap))

 theorem raw_lower_continuous {X sigma sigmap mu C7 C8 T h : ℝ}
    (hs : sigmap≠1) (hh : h<T) :
    ContinuousAt (rawRectangleBound X sigma sigmap mu C7 C8 T) h := by
  have hden : T-h≠0 := (sub_pos.mpr hh).ne'
  have hc := (actual_F_endpoint_continuous hs X).continuousAt (x:=h)
  have hn := actual_F_difference_nonneg hs X hh.le
  have harg : 0<1+(cumulativeSquare X sigmap T-cumulativeSquare X sigmap h)/(T-h) := by positivity
  unfold rawRectangleBound
  have hfrac : ContinuousAt (fun u : ℝ =>
      1+(cumulativeSquare X sigmap T-cumulativeSquare X sigmap u)/(T-u)) h := by
    exact continuousAt_const.add ((continuousAt_const.sub hc).div (continuousAt_const.sub continuousAt_id) hden)
  have hlogcont : ContinuousAt (fun u : ℝ =>
      log (1+(cumulativeSquare X sigmap T-cumulativeSquare X sigmap u)/(T-u))) h :=
    hfrac.log harg.ne'
  exact (((continuousAt_const.sub continuousAt_id).mul hlogcont).add continuousAt_const).div_const _

 theorem raw_C7_mono {X sigma sigmap mu C7 C7' C8 T h : ℝ}
    (hgap : sigmap<sigma) (hmu : sigmap≤mu) (hT : 1≤T) (hC : C7≤C7') :
    rawRectangleBound X sigma sigmap mu C7 C8 T h≤rawRectangleBound X sigma sigmap mu C7' C8 T h := by
  have hl : 0≤log T := log_nonneg hT
  have hprod := mul_le_mul_of_nonneg_right hC (sub_nonneg.mpr hmu)
  have hplus : C7*(mu-sigmap)+C8/2≤C7'*(mu-sigmap)+C8/2 := by linarith
  have hlogs := mul_le_mul_of_nonneg_right hplus hl
  unfold rawRectangleBound
  apply div_le_div_of_nonneg_right _ (by positivity : 0≤2*Real.pi*(sigma-sigmap))
  linarith

 theorem actual_low_count_zero (hRH : IEANTN.RiemannHypothesisUpTo height)
    {sigma h : ℝ} (hs : (3/4:ℝ)≤sigma) (hh : h≤height) : IEANTN.zetaN' sigma h=0 := by
  have he : IsEmpty (IEANTN.zetaZeroesIn (Ioo sigma 1) (Ioo 0 h)) := by
    refine ⟨fun z => ?_⟩
    apply hRH.false
    exact ⟨z,⟨⟨by linarith [z.property.1.1],z.property.1.2⟩,
      ⟨z.property.2.1.1.le,z.property.2.1.2.le.trans hh⟩,z.property.2.2⟩⟩
  letI := he
  simp [IEANTN.zetaN',IEANTN.zetaZeroesSum]

/-- Exact selected Hstar specialization of the independent original rectangle
relation. The sole analytic source input is required only at regular lower edges;
it contains neither the new U nor a new zero-density conclusion. -/
theorem selected_lower_contour
    (hRH : IEANTN.RiemannHypothesisUpTo height) {sigma T : ℝ}
    (hs : (3/4:ℝ)≤sigma) (hs' : sigma≤7/8) (hT : height≤T)
    (hSourceRectangle : ∃ E : Set ℝ, E.Countable ∧ ∀ h : ℝ,
      height-1<h → h<height → h∉E →
      IEANTN.zetaN' sigma T-IEANTN.zetaN' sigma h≤
        rawRectangleBound T sigma (sigma-(851/2500)/log T) (1237/1000)
          (cSevenAt eulerMascheroniConstant h) (sourceCEight eulerMascheroniConstant) T h) :
    IEANTN.zetaN' sigma T≤
      rawRectangleBound T sigma (sigma-(851/2500)/log T) (1237/1000)
        (sourceCSeven eulerMascheroniConstant) (sourceCEight eulerMascheroniConstant) T (height-1) := by
  obtain ⟨E,hE,hsource⟩:=hSourceRectangle
  have hT1 : 1<T := lt_of_lt_of_le (by norm_num [height]) hT
  have hlog : 0<log T := log_pos hT1
  have hq : 0<(851/2500:ℝ)/log T := by positivity
  have hsne : sigma-(851/2500)/log T≠1 := by linarith
  have hgap : sigma-(851/2500)/log T<sigma := by linarith
  have hmu : sigma-(851/2500)/log T≤(1237/1000:ℝ) := by linarith
  apply limit_from_regular_lower_edges (H0:=height) (E:=E) (by linarith) hE
    (raw_lower_continuous hsne (by linarith))
  intro h hh hh' hnot
  have hc := hsource h hh hh' hnot
  rw [actual_low_count_zero hRH hs hh'.le,sub_zero] at hc
  apply hc.trans
  apply raw_C7_mono hgap hmu hT1.le
  rw [←cSevenAt_selected]
  exact cSevenAt_antitone eulerMascheroniConstant (by norm_num [height]) hh.le

#print axioms actual_F_endpoint_continuous
#print axioms raw_lower_continuous
#print axioms selected_lower_contour
end WinnerLowerContour
