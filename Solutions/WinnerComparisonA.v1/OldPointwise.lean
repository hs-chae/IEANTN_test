/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldContinuity
import OldVSource
import OldOuterSemantics
namespace WinnerOldC4Source
open Real Set MeasureTheory
open WinnerOldFloors
set_option maxHeartbeats 0
noncomputable def d : ℝ := 3663/10000
noncomputable def interp (s u : ℝ) : ℝ :=
  2*(1-s)+(2*d+2*delta*(2*s-1))/(u+2*delta)
noncomputable def leftD (U V u : ℝ) : ℝ := log (U/V)+log u+4*u/3
noncomputable def logModel (U V s u : ℝ) : ℝ :=
  log V+2*log u+interp s u*leftD U V u-u
noncomputable def aSlope (u : ℝ) : ℝ := 2-4*delta/(u+2*delta)

 theorem interp_nonneg {s u : ℝ} (hs : (3/4:ℝ)≤s) (hs' : s≤7/8) (hu : 0<u) :
    0≤ interp s u := by
  have hp : 0≤2*d+2*delta*(2*s-1) := by unfold d delta;nlinarith
  have hden : 0<u+2*delta := by unfold delta;positivity
  unfold interp
  have hd:=div_nonneg hp hden.le
  linarith

 theorem interp_le_one {s u : ℝ} (hs : (3/4:ℝ)≤s) (hs' : s≤7/8) (hu : h≤u) :
    interp s u≤1 := by
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hden : 0<u+2*delta := by unfold delta;linarith
  have hp:=mul_le_mul_of_nonneg_right hs (by linarith : 0≤u)
  have hc : 2*d+2*delta*(2*s-1)≤(1-2*(1-s))*(u+2*delta) := by
    unfold d delta at *
    nlinarith
  have hh := (div_le_iff₀ hden).mpr hc
  unfold interp
  linarith

 theorem interp_antitone_height {s ul ur : ℝ}
    (hs : (3/4:ℝ)≤s) (hs' : s≤7/8) (hl : 0<ul) (hlu : ul≤ur) :
    interp s ur≤ interp s ul := by
  have hp : 0≤2*d+2*delta*(2*s-1) := by unfold d delta;nlinarith
  unfold interp
  have hh : (2*d+2*delta*(2*s-1))/(ur+2*delta)≤
      (2*d+2*delta*(2*s-1))/(ul+2*delta) :=
    div_le_div_of_nonneg_left hp (by unfold delta;positivity) (by linarith)
  linarith

 theorem leftD_monotone {U V ul ur : ℝ} (hl : 0<ul) (hlu : ul≤ur) :
    leftD U V ul≤leftD U V ur := by
  have hlog:=log_le_log hl hlu
  unfold leftD
  linarith

 theorem leftD_pos {U V u : ℝ} (hU : (8/5:ℝ)≤U) (hV : 0<V) (hV' : V≤8) (hu : h≤u) :
    0<leftD U V u := by
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hup : 0<u := by linarith
  have hUp : 0<U := by linarith
  have hr := neg_inv_le_log (div_nonneg hUp.le hV.le)
  have hrat : V/U≤5 := (div_le_iff₀ hUp).mpr (by linarith)
  have he : (U/V)⁻¹=V/U := by field_simp
  rw [he] at hr
  have hl : 0≤log u := log_nonneg (by linarith)
  unfold leftD
  linarith

 theorem logModel_centered {U V s beta u : ℝ} (hu : 0<u) :
    logModel U V s u=logModel U V beta u+aSlope u*leftD U V u*(beta-s) := by
  unfold logModel interp aSlope
  have hden : u+2*delta≠0 := by unfold delta;positivity
  field_simp [hden]
  <;> ring

 theorem logModel_lower {U V s ul u ur : ℝ}
    (hU : (8/5:ℝ)≤U) (hV : 0<V) (hV' : V≤8)
    (hs : (3/4:ℝ)≤s) (hs' : s≤7/8)
    (hl : h≤ul) (hlu : ul≤u) (hur : u≤ur) :
    log V+2*log ul+interp s ur*leftD U V ul-ur≤logModel U V s u := by
  have hhp : 0<h := by linarith [h_lower]
  have hlp : 0<ul := hhp.trans_le hl
  have hup : 0<u := hlp.trans_le hlu
  have hρ:=interp_antitone_height hs hs' hup hur
  have hprod:=mul_le_mul hρ (leftD_monotone hlp hlu)
    (leftD_pos hU hV hV' hl).le (interp_nonneg hs hs' hup)
  have hlog:=log_le_log hlp hlu
  unfold logModel
  nlinarith

 theorem logModel_upper {U V s ul u ur : ℝ}
    (hU : (8/5:ℝ)≤U) (hV : 0<V) (hV' : V≤8)
    (hs : (3/4:ℝ)≤s) (hs' : s≤7/8)
    (hl : h≤ul) (hlu : ul≤u) (hur : u≤ur) :
    logModel U V s u≤log V+2*log ur+interp s ul*leftD U V ur-ul := by
  have hhp : 0<h := by linarith [h_lower]
  have hlp : 0<ul := hhp.trans_le hl
  have hup : 0<u := hlp.trans_le hlu
  have hρ:=interp_antitone_height hs hs' hlp hlu
  have hprod:=mul_le_mul hρ (leftD_monotone hup hur)
    (leftD_pos hU hV hV' (hl.trans hlu)).le (interp_nonneg hs hs' hlp)
  have hlog:=log_le_log hup hur
  unfold logModel
  nlinarith

#print axioms logModel_lower
#print axioms logModel_upper
#print axioms logModel_centered
end WinnerOldC4Source
