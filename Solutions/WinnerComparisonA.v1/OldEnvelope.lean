/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldWindow
import OuterAssembly
namespace WinnerOldC4Source
open Real Set MeasureTheory
open WinnerOldFloors WinnerOldOuter.Assembly
set_option maxHeartbeats 0
noncomputable def heightRatio (v : ℝ) : ℝ := 1-exp (-v)+exp (-(h+v))
noncomputable def zModel (U V s u : ℝ) : ℝ := omegaFactor s u*exp (logModel U V s u)
noncomputable def countModel (U V s v : ℝ) : ℝ :=
  ((h+v)/(2*Real.pi*d))*(heightRatio v*log (1+zModel U V s (h+v)/heightRatio v))
noncomputable def oldMain (s v : ℝ) : ℝ := countModel (oldU (h+v)) (oldV (h+v)) s v
/-- Positive lower witness for the full old density/count-window expression.
It is not itself asserted to upper-bound N: the original boundary/count-error
allowances are positive and omitted only when lower-enclosing the old bound. -/
noncomputable def oldLowerWitness (s v : ℝ) : ℝ := min (oldMain s v) (windowMain v)
noncomputable def weightedWitness (s v : ℝ) : ℝ := exp ((601/2:ℝ)*(s-7/8))*oldLowerWitness s v

 theorem interp_centered {s beta u : ℝ} (hu : 0<u) :
    interp s u=interp beta u+aSlope u*(beta-s) := by
  unfold interp aSlope
  have hden : u+2*delta≠0 := by unfold delta;positivity
  field_simp [hden]
  <;> ring

 theorem heightRatio_pos {v : ℝ} (hv : 0≤v) : 0<heightRatio v := by
  have he : exp (-v)≤1 := exp_le_one_iff.mpr (by linarith)
  unfold heightRatio
  linarith [exp_pos (-(h+v))]

 theorem countModel_mono {U V U' V' s v : ℝ}
    (hU : 0<U) (hV : 0<V) (hUU : U≤U') (hVV : V≤V')
    (hs : (3/4:ℝ)≤s) (hs' : s≤7/8) (hv : 0≤v) :
    countModel U V s v≤countModel U' V' s v := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<h+v := by positivity
  have hlu : h≤h+v := by linarith
  have hUp : 0<U' := hU.trans_le hUU
  have hVp : 0<V' := hV.trans_le hVV
  have ha:=interp_nonneg hs hs' hup
  have hb : 0≤1-interp s (h+v) := by linarith [interp_le_one hs hs' hlu]
  have hlogU:=mul_le_mul_of_nonneg_left (log_le_log hU hUU) ha
  have hlogV:=mul_le_mul_of_nonneg_left (log_le_log hV hVV) hb
  have hm : logModel U V s (h+v)≤logModel U' V' s (h+v) := by
    unfold logModel leftD
    rw [log_div hU.ne' hV.ne',log_div hUp.ne' hVp.ne']
    nlinarith
  have hOm : 0≤omegaFactor s (h+v) := by unfold omegaFactor smoothingR;positivity
  have hzm : zModel U V s (h+v)≤zModel U' V' s (h+v) :=
    mul_le_mul_of_nonneg_left (exp_le_exp.mpr hm) hOm
  have hr:=heightRatio_pos hv
  have hz : 0≤zModel U V s (h+v) := by unfold zModel;positivity
  have harg : 0<1+zModel U V s (h+v)/heightRatio v := by positivity
  have hl := log_le_log harg (show 1+zModel U V s (h+v)/heightRatio v≤
      1+zModel U' V' s (h+v)/heightRatio v by gcongr)
  unfold countModel
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl hr.le)
    (by unfold d;positivity)

 theorem cell_z_bounds {v0 step U V v s : ℝ} {k : ℕ}
    (hv0 : 0≤v0) (hstep : 0≤step)
    (hU : (8/5:ℝ)≤U) (hV : 0<V) (hV' : V≤8)
    (hs : (3/4:ℝ)≤s) (hs' : s≤7/8)
    (hvl : v0+step*k≤v) (hvr : v≤v0+step*(k+1)) :
    (rowData v0 step U V k).zl*exp ((rowData v0 step U V k).Bl*(7/8-s))≤zModel U V s (h+v) ∧
      zModel U V s (h+v)≤(rowData v0 step U V k).zu*exp ((rowData v0 step U V k).Bu*(7/8-s)) := by
  let ul:=h+(v0+step*k)
  let ur:=h+(v0+step*k+step)
  have hh : 0<h := by linarith [h_lower]
  have h0l : h≤ul := by
    dsimp [ul]
    have hn : 0≤v0+step*k := by positivity
    linarith
  have hlp : 0<ul := hh.trans_le h0l
  have hvp : 0≤v := by
    have h0 : 0≤v0+step*k := by positivity
    linarith
  have hlu : ul≤h+v := by dsimp [ul];linarith
  have hur : h+v≤ur := by dsimp [ur];push_cast at hvr;linarith
  have hurp : 0<ur := (hh.trans_le (by linarith : h≤h+v)).trans_le hur
  have hLo:=logModel_lower hU hV hV' hs hs' h0l hlu hur
  have hHi:=logModel_upper hU hV hV' hs hs' h0l hlu hur
  have hOmega:=omegaFactor_bounds hs hs' (show h≤h+v by linarith)
  have hcL:=interp_centered (s:=s) (beta:=7/8) hurp
  have hcU:=interp_centered (s:=s) (beta:=7/8) hlp
  have hzl : (rowData v0 step U V k).zl*exp ((rowData v0 step U V k).Bl*(7/8-s))=
      (499999/1000000:ℝ)*exp (2*alpha)*exp (log V+2*log ul+interp s ur*leftD U V ul-ur) := by
    rw [hcL]
    dsimp only [rowData]
    change (499999/1000000:ℝ)*exp (2371/10000+
      (1/4+(2*(3663/10000)+2*(3599/10000)*(2*(7/8)-1))/(ur+3599/5000))*
        leftD U V ul+log V+2*log ul-ur)*exp ((2-(3599/2500)/(ur+3599/5000))*leftD U V ul*(7/8-s))=_
    unfold interp aSlope alpha delta d
    simp only [mul_assoc,←exp_add]
    congr 2
    ring
  have hzu : (rowData v0 step U V k).zu*exp ((rowData v0 step U V k).Bu*(7/8-s))=
      (501/1000:ℝ)*exp (2*alpha)*exp (log V+2*log ur+interp s ul*leftD U V ur-ul) := by
    rw [hcU]
    dsimp only [rowData]
    change (501/1000:ℝ)*exp (2371/10000+
      (1/4+(2*(3663/10000)+2*(3599/10000)*(2*(7/8)-1))/(ul+3599/5000))*
        leftD U V ur+log V+2*log ur-ul)*exp ((2-(3599/2500)/(ul+3599/5000))*leftD U V ur*(7/8-s))=_
    unfold interp aSlope alpha delta d
    simp only [mul_assoc,←exp_add]
    congr 2
    ring
  rw [hzl,hzu]
  constructor
  · exact mul_le_mul hOmega.1 (exp_le_exp.mpr hLo) (exp_pos _).le (by unfold omegaFactor smoothingR;positivity)
  · exact mul_le_mul hOmega.2 (exp_le_exp.mpr hHi) (exp_pos _).le (by positivity)

#print axioms countModel_mono
#print axioms cell_z_bounds
end WinnerOldC4Source
