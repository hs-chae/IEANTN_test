/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongContinuity
import StrongUCoarse
import StrongPointwise
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors
set_option maxHeartbeats 0
noncomputable def main (s v : ℝ) : ℝ := WinnerOldC4Source.countModel
  (WinnerStrongC4Source.oldU (h+v)) (WinnerOldC4Source.oldV (h+v)) s v
noncomputable def witness (s v : ℝ) : ℝ := min (main s v) (WinnerOldC4Source.windowMain v)
noncomputable def weighted (s v : ℝ) : ℝ := exp ((30001/100:ℝ)*(s-7/8))*witness s v
 theorem U_positive {v : ℝ} (hv : 0≤v) (hv' : v≤16) : 0<WinnerStrongC4Source.oldU (h+v) := by
  have hf:=WinnerStrongC4Source.floorU_lower hv hv'
  have hb:=WinnerStrongC4Source.oldU_floor hv (show h≤h+v by linarith) (show h+v≤h+v by rfl)
  linarith
 theorem V_positive {v : ℝ} (hv : 0≤v) : 0<WinnerOldC4Source.oldV (h+v) := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<h+v := by positivity
  have hm:=WinnerOldC4Source.mzero_pos
  unfold WinnerOldC4Source.oldV WinnerOldC4Source.cfive WinnerOldC4Source.csix
    WinnerOldC4Source.delta WinnerOldC4Source.alpha
  positivity
 theorem nonnegative {s v : ℝ} (hv : 0≤v) : 0≤weighted s v := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<h+v := by positivity
  have hr:=WinnerOldC4Source.heightRatio_pos hv
  have hz : 0≤WinnerOldC4Source.zModel (WinnerStrongC4Source.oldU (h+v)) (WinnerOldC4Source.oldV (h+v)) s (h+v) := by
    unfold WinnerOldC4Source.zModel WinnerOldC4Source.omegaFactor WinnerOldC4Source.smoothingR
    positivity
  have hl : 0≤log (1+WinnerOldC4Source.zModel (WinnerStrongC4Source.oldU (h+v)) (WinnerOldC4Source.oldV (h+v)) s (h+v)/WinnerOldC4Source.heightRatio v) :=
    log_nonneg (by linarith [div_nonneg hz hr.le])
  have hm : 0≤main s v := by
    unfold main WinnerOldC4Source.countModel
    have hd : 0≤(h+v)/(2*Real.pi*WinnerOldC4Source.d) := by unfold WinnerOldC4Source.d;positivity
    exact mul_nonneg hd (mul_nonneg hr.le hl)
  have hw : 0≤WinnerOldC4Source.windowMain v := by
    have hw:=WinnerOldC4Source.windowMain_monotone hv
    simpa [WinnerOldC4Source.windowMain] using hw
  unfold weighted witness
  positivity
 theorem main_continuousAt {p : ℝ×ℝ} (hv : 0<p.2) (hv' : p.2≤16) :
    ContinuousAt (fun q:ℝ×ℝ=>main q.1 q.2) p := by
  have hh : 0<h := by linarith [h_lower]
  have hu : h<h+p.2 := by linarith
  have hup : 0<h+p.2 := by positivity
  have hu0 : h+p.2≠0 := hup.ne'
  have hU : ContinuousAt WinnerStrongC4Source.oldU (h+p.2) :=
    WinnerStrongC4Source.oldU_continuousOn.continuousAt (Ici_mem_nhds hu)
  have hUc : ContinuousAt (fun q:ℝ×ℝ=>WinnerStrongC4Source.oldU (h+q.2)) p :=
    ContinuousAt.comp (x:=p) (g:=WinnerStrongC4Source.oldU) (f:=fun q:ℝ×ℝ=>h+q.2) hU (show ContinuousAt (fun q:ℝ×ℝ=>h+q.2) p by fun_prop)
  have hV : ContinuousAt WinnerOldC4Source.oldV (h+p.2) := by
    unfold WinnerOldC4Source.oldV WinnerOldC4Source.cfive WinnerOldC4Source.csix
      WinnerOldC4Source.delta WinnerOldC4Source.alpha
    fun_prop (disch:=first |assumption|positivity)
  have hVc : ContinuousAt (fun q:ℝ×ℝ=>WinnerOldC4Source.oldV (h+q.2)) p :=
    ContinuousAt.comp (x:=p) (g:=WinnerOldC4Source.oldV) (f:=fun q:ℝ×ℝ=>h+q.2) hV
      (show ContinuousAt (fun q:ℝ×ℝ=>h+q.2) p by fun_prop)
  have hUp:=U_positive hv.le hv'
  have hVp:=V_positive hv.le
  have hU0:=hUp.ne'
  have hV0:=hVp.ne'
  have hUV0 : WinnerStrongC4Source.oldU (h+p.2)/WinnerOldC4Source.oldV (h+p.2)≠0 := div_ne_zero hU0 hV0
  have hr:=WinnerOldC4Source.heightRatio_pos hv.le
  have hr0:=hr.ne'
  have hz : 0<WinnerOldC4Source.zModel (WinnerStrongC4Source.oldU (h+p.2)) (WinnerOldC4Source.oldV (h+p.2)) p.1 (h+p.2) := by
    unfold WinnerOldC4Source.zModel WinnerOldC4Source.omegaFactor WinnerOldC4Source.smoothingR
    positivity
  have harg : 1+WinnerOldC4Source.zModel (WinnerStrongC4Source.oldU (h+p.2)) (WinnerOldC4Source.oldV (h+p.2)) p.1 (h+p.2)/WinnerOldC4Source.heightRatio p.2≠0 := by positivity
  have hd : 2*Real.pi*WinnerOldC4Source.d≠0 := by unfold WinnerOldC4Source.d;positivity
  have hshift : h+p.2+2*WinnerOldC4Source.delta≠0 := by unfold WinnerOldC4Source.delta;positivity
  unfold main WinnerOldC4Source.countModel WinnerOldC4Source.zModel WinnerOldC4Source.logModel
    WinnerOldC4Source.leftD WinnerOldC4Source.omegaFactor WinnerOldC4Source.interp WinnerOldC4Source.heightRatio
  fun_prop (disch:=first |assumption|positivity)
 theorem continuousOn_rectangle : ContinuousOn (fun p:ℝ×ℝ=>weighted p.1 p.2)
    (Icc (33/40:ℝ) (7/8) ×ˢ Icc (1/10000:ℝ) 16) := by
  intro p hp
  have hv : 0<p.2 := by linarith [hp.2.1]
  apply ContinuousAt.continuousWithinAt
  unfold weighted witness
  apply ContinuousAt.mul (by fun_prop)
  have hw : ContinuousAt (fun q:ℝ×ℝ=>WinnerOldC4Source.windowMain q.2) p := by
    unfold WinnerOldC4Source.windowMain
    fun_prop
  exact (main_continuousAt hv hp.2.2).min hw
#print axioms continuousOn_rectangle
end WinnerStrongEnvelope
