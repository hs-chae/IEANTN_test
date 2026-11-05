import OldEnvelope
namespace WinnerStrongBounds
open Real Set MeasureTheory WinnerOldFloors WinnerOldOuter.Assembly WinnerOldC4Source
set_option maxHeartbeats 0
 theorem leftD_pos {U V u : ℝ} (hU : (1:ℝ)≤U) (hV : 0<V) (hV' : V≤8) (hu : h≤u) :
    0<leftD U V u := by
  have hu28 : (28:ℝ)≤u := h_lower.trans hu
  have hup : 0<u := by linarith
  have hUp : 0<U := by linarith
  have hr := neg_inv_le_log (div_nonneg hUp.le hV.le)
  have hrat : V/U≤8 := (div_le_iff₀ hUp).mpr (by linarith)
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
    (hU : (1:ℝ)≤U) (hV : 0<V) (hV' : V≤8)
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
    (hU : (1:ℝ)≤U) (hV : 0<V) (hV' : V≤8)
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

 theorem cell_z_bounds {v0 step U V v s : ℝ} {k : ℕ}
    (hv0 : 0≤v0) (hstep : 0≤step)
    (hU : (1:ℝ)≤U) (hV : 0<V) (hV' : V≤8)
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


#print axioms cell_z_bounds
end WinnerStrongBounds
