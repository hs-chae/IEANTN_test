/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongAllowance
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors
set_option maxHeartbeats 0
attribute [local fun_prop] ContinuousWithinAt.prodMk ContinuousWithinAt.log

 theorem floorU_positive_all {v : ℝ} (hv : 0 ≤ v) : 0<WinnerStrongC4Source.floorU v := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<h+v := by positivity
  have hr:=ratio_nonneg hv
  have hz : 0 ≤ WinnerStrongC4Source.oldRzero (h+v) := by
    unfold WinnerStrongC4Source.oldRzero WinnerStrongC4Source.a2 WinnerStrongC4Source.a1 WinnerStrongC4Source.a3
    positivity
  have hc : 0<WinnerStrongC4Source.oldC4 (h+v) := by
    unfold WinnerStrongC4Source.oldC4 WinnerStrongC4Source.a1 WinnerStrongC4Source.a3
    positivity
  have hj0 : 0<WinnerStrongC4.momentLower 0 := by norm_num [WinnerStrongC4.momentLower]
  have hj1:=WinnerStrongC4.moment_lower_nonneg 1
  have hj2:=WinnerStrongC4.moment_lower_nonneg 2
  have hj3:=WinnerStrongC4.moment_lower_nonneg 3
  have hj4:=WinnerStrongC4.moment_lower_nonneg 4
  have hj5:=WinnerStrongC4.moment_lower_nonneg 5
  have hj6:=WinnerStrongC4.moment_lower_nonneg 6
  have hj7:=WinnerStrongC4.moment_lower_nonneg 7
  have hj8:=WinnerStrongC4.moment_lower_nonneg 8
  have hj9:=WinnerStrongC4.moment_lower_nonneg 9
  have hj10:=WinnerStrongC4.moment_lower_nonneg 10
  have hj11:=WinnerStrongC4.moment_lower_nonneg 11
  unfold WinnerStrongC4Source.floorU WinnerStrongC4.expanded WinnerStrongC4Source.alpha
  positivity
 theorem U_positive_all {v : ℝ} (hv : 0 ≤ v) : 0<WinnerStrongC4Source.oldU (h+v) :=
  (floorU_positive_all hv).trans_le (WinnerStrongC4Source.oldU_floor hv (by linarith) le_rfl)
 noncomputable def weightedAllowance (L s v : ℝ) : ℝ := exp (L*(s-7/8))*allowance s v
 theorem full_regular (L lo hi b : ℝ) : ContinuousOn (fun p:ℝ×ℝ=>weightedAllowance L p.1 p.2)
      (Icc lo hi ×ˢ Icc (0:ℝ) b) := by
  let S:=Icc lo hi ×ˢ Icc (0:ℝ) b
  have hUOn : ContinuousOn (fun p:ℝ×ℝ=>WinnerStrongC4Source.oldU (h+p.2)) S := by
    apply WinnerStrongC4Source.oldU_continuousOn.comp
      (show ContinuousOn (fun p:ℝ×ℝ=>h+p.2) S from (continuous_const.add continuous_snd).continuousOn)
    intro p hp
    exact show h ≤ h+p.2 by linarith [hp.2.1]
  intro p hp
  have hpS : p∈S := hp
  have hv : 0 ≤ p.2 := hp.2.1
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<h+p.2 := by positivity
  have hu0:=hup.ne'
  have hfst : ContinuousWithinAt (fun q:ℝ×ℝ=>q.1) S p := continuous_fst.continuousAt.continuousWithinAt
  have hsnd : ContinuousWithinAt (fun q:ℝ×ℝ=>q.2) S p := continuous_snd.continuousAt.continuousWithinAt
  have hUc:=hUOn p hpS
  have hVAt : ContinuousAt WinnerOldC4Source.oldV (h+p.2) := by
    unfold WinnerOldC4Source.oldV WinnerOldC4Source.cfive WinnerOldC4Source.csix
      WinnerOldC4Source.delta WinnerOldC4Source.alpha
    fun_prop (disch:=first |assumption|positivity)
  have hVc : ContinuousWithinAt (fun q:ℝ×ℝ=>WinnerOldC4Source.oldV (h+q.2)) S p :=
    (ContinuousAt.comp (x:=p) (g:=WinnerOldC4Source.oldV) (f:=fun q:ℝ×ℝ=>h+q.2) hVAt
      (show ContinuousAt (fun q:ℝ×ℝ=>h+q.2) p by fun_prop)).continuousWithinAt
  have hUp:=U_positive_all hv
  have hVp:=V_positive hv
  have hU0:=hUp.ne'
  have hV0:=hVp.ne'
  have hUV0 : WinnerStrongC4Source.oldU (h+p.2)/WinnerOldC4Source.oldV (h+p.2)≠0 := div_ne_zero hU0 hV0
  have hr:=WinnerOldC4Source.heightRatio_pos hv
  have hr0:=hr.ne'
  have hz : 0<WinnerOldC4Source.zModel (WinnerStrongC4Source.oldU (h+p.2)) (WinnerOldC4Source.oldV (h+p.2)) p.1 (h+p.2) := by
    unfold WinnerOldC4Source.zModel WinnerOldC4Source.omegaFactor WinnerOldC4Source.smoothingR
    positivity
  have harg : 1+WinnerOldC4Source.zModel (WinnerStrongC4Source.oldU (h+p.2)) (WinnerOldC4Source.oldV (h+p.2)) p.1 (h+p.2)/WinnerOldC4Source.heightRatio p.2≠0 := by positivity
  have hd : 2*Real.pi*WinnerOldC4Source.d≠0 := by unfold WinnerOldC4Source.d;positivity
  have hshift : h+p.2+2*WinnerOldC4Source.delta≠0 := by unfold WinnerOldC4Source.delta;positivity
  change ContinuousWithinAt (fun p:ℝ×ℝ=>weightedAllowance L p.1 p.2) S p
  unfold weightedAllowance allowance main WinnerOldC4Source.countModel WinnerOldC4Source.zModel
    WinnerOldC4Source.logModel WinnerOldC4Source.leftD WinnerOldC4Source.omegaFactor
    WinnerOldC4Source.interp WinnerOldC4Source.heightRatio boundaryAllowance windowAllowance rosserError WinnerOldC4Source.windowMain
  fun_prop (disch:=first |assumption|positivity)
 theorem witness_nonnegative {s v : ℝ} (hv : 0 ≤ v) : 0 ≤ witness s v :=
  nonneg_of_mul_nonneg_right (nonnegative (s:=s) hv) (exp_pos _)
 theorem allowance_nonnegative {s v : ℝ} (hs : s ≤ 7/8) (hv : 0 ≤ v) : 0 ≤ allowance s v :=
  (witness_nonnegative hv).trans (witness_le_full_allowance hs hv)
 theorem weightedAllowance_nonnegative {L s v : ℝ} (hs : s ≤ 7/8) (hv : 0 ≤ v) :
    0 ≤ weightedAllowance L s v := mul_nonneg (exp_pos _).le (allowance_nonnegative hs hv)
#print axioms full_regular
end WinnerStrongEnvelope
