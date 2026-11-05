/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongCell
import WarmPade
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors WinnerOldC4Source WinnerOldOuter.Assembly
set_option maxHeartbeats 0
noncomputable def softMinReal (a b : ℝ) : ℝ :=
  (a+b-sqrt ((a-b)^2+(1/1000000000000:ℝ)^2))/2
 theorem softMinReal_le (a b : ℝ) : softMinReal a b ≤ min a b := by
  have hh : |a-b| ≤ sqrt ((a-b)^2+(1/1000000000000:ℝ)^2) := by
    have hs:=sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg (1/1000000000000:ℝ)) :
      (a-b)^2 ≤ (a-b)^2+(1/1000000000000:ℝ)^2)
    simpa only [sqrt_sq_eq_abs] using hs
  have ha: a-b ≤ sqrt ((a-b)^2+(1/1000000000000:ℝ)^2) := (le_abs_self _).trans hh
  have hb: b-a ≤ sqrt ((a-b)^2+(1/1000000000000:ℝ)^2) := by
    have hb:=neg_le_abs (a-b)
    linarith
  unfold softMinReal
  exact le_min (by linarith) (by linarith)
noncomputable def rhiReal (vl vr : ℝ) : ℝ := 1-exp (-vr)+exp (-(h+vl))
noncomputable def fmaxReal (v0 step b : ℝ) (k : ℕ) : ℝ :=
  let c:=data v0 step k
  let vl:=v0+step*k
  let vr:=vl+step
  let zmax:=c.zl*exp (c.Bl*b)
  (c.ul*c.rmin*(2*zmax))/(((3663/5000)*Real.pi)*(2*rhiReal vl vr+zmax))
noncomputable def warmCell (v0 step a b : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  let c:=data v0 step k
  exp ((30001/100:ℝ)*(s-7/8))*
    softMinReal (fmaxReal v0 step b k) (windowMain (v0+step*k))*
    exp (-c.Bl*b)*exp (c.Bl*(7/8-s))

 theorem warm_cell_lower {v0 step a b s v : ℝ} {k : ℕ}
    (hv0 : 0<v0) (hstep : 0 ≤ step) (hmax : v0+step*(k+1) ≤ 16)
    (hs0 : (3/4:ℝ) ≤ s) (hs1 : s ≤ 7/8) (hs2 : 7/8-b ≤ s)
    (hvlv : v0+step*k ≤ v) (hvvr : v ≤ v0+step*(k+1)) :
    warmCell v0 step a b k s ≤ weighted s v := by
  let vl:=v0+step*k
  let vr:=vl+step
  let U:=WinnerStrongC4Source.floorU vr
  let V:=WinnerStrongV.floorV vl vr
  let c:=data v0 step k
  let den:ℝ:=(3663/5000)*Real.pi
  let z:=c.zl*exp (c.Bl*(7/8-s))
  let zm:=c.zl*exp (c.Bl*b)
  let rh:=rhiReal vl vr
  let fm:=fmaxReal v0 step b k
  let gg:=exp (c.Bl*((7/8-s)-b))
  have hden : 0<den := by dsimp [den];positivity
  have hvl : 0<vl := by dsimp [vl];positivity
  have hvr : 0<vr := by dsimp [vr];positivity
  have hvr16 : vr ≤ 16 := by dsimp [vr,vl];push_cast at hmax ⊢;linarith
  have hvlv' : vl ≤ v := hvlv
  have hvvr' : v ≤ vr := by dsimp [vr,vl];push_cast at hvvr ⊢;linarith
  have hvp : 0 ≤ v := hvl.le.trans hvlv'
  have hU : (1:ℝ) ≤ U := WinnerStrongC4Source.floorU_lower hvr.le hvr16
  have hUp : 0<U := by linarith
  have hV : 0<V := WinnerStrongV.floorV_positive hvl.le hvr.le
  have hV8 : V ≤ 8 := WinnerStrongV.floorV_upper hvl.le hvr.le
  have hcz:=WinnerStrongBounds.cell_z_bounds hv0.le hstep hU hV hV8 hs0 hs1 hvlv hvvr
  change z ≤ zModel U V s (h+v) ∧ _ at hcz
  have hul : 0<c.ul := by change 0<h+vl;linarith [h_lower]
  have hlu : c.ul ≤ h+v := by change h+vl ≤ h+v;linarith
  have hrmin : 0<c.rmin := by
    change 0<1-exp (-vl)
    have he:exp (-vl)<1 := exp_lt_one_iff.mpr (by linarith)
    linarith
  have hratio : c.rmin ≤ heightRatio v := by
    have he:exp (-v) ≤ exp (-vl) := exp_le_exp.mpr (by linarith)
    change 1-exp (-vl) ≤ 1-exp (-v)+exp (-(h+v))
    linarith [exp_pos (-(h+v))]
  have hrh : heightRatio v ≤ rh := by
    have he1:exp (-vr) ≤ exp (-v) := exp_le_exp.mpr (by linarith)
    have he2:exp (-(h+v)) ≤ exp (-(h+vl)) := exp_le_exp.mpr (by linarith)
    dsimp [heightRatio,rh,rhiReal]
    linarith
  have hrp:=heightRatio_pos hvp
  have hrhp : 0<rh := hrp.trans_le hrh
  have hzc : 0<c.zl := by dsimp [c,data,rowData];positivity
  have hzp : 0<z := by dsimp [z];positivity
  have hzmp : 0<zm := by dsimp [zm];positivity
  have hBl:=data_Bl_nonneg hv0.le hstep hmax
  have hzm : z ≤ zm := by
    dsimp [z,zm]
    exact mul_le_mul_of_nonneg_left (exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (by linarith) hBl)) hzc.le
  have hP:=WinnerWarmPade.log_count_lower hrmin.le hratio hrp hrh hzp.le hcz.1
  have hfix : c.rmin*2*z/(2*rh+zm) ≤ c.rmin*2*z/(2*rh+z) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hpersp : 0 ≤ heightRatio v*log (1+zModel U V s (h+v)/heightRatio v) := by
    have hz0:0 ≤ zModel U V s (h+v) := hzp.le.trans hcz.1
    exact mul_nonneg hrp.le (log_nonneg (by linarith [div_nonneg hz0 hrp.le]))
  have hfixed : c.ul*(c.rmin*2*z/(2*rh+zm))/den ≤ countModel U V s v := by
    have hn:=mul_le_mul hlu (hfix.trans hP) (by positivity : 0 ≤ c.rmin*2*z/(2*rh+zm))
      (show 0 ≤ h+v by linarith [h_lower])
    have hd:=div_le_div_of_nonneg_right hn hden.le
    convert! hd using 1
    unfold countModel d
    dsimp [den]
    ring
  have hUf : U ≤ WinnerStrongC4Source.oldU (h+v) :=
    WinnerStrongC4Source.oldU_floor hvr.le (show h ≤ h+v by linarith) (by linarith)
  have hVf : V ≤ WinnerOldC4Source.oldV (h+v) :=
    WinnerStrongV.oldV_floor hvl.le (by dsimp [vr];linarith) (by linarith) (by linarith)
  have hmono:=countModel_mono hUp hV hUf hVf hs0 hs1 hvp
  have hfm : 0<fm := by change 0<c.ul*c.rmin*(2*zm)/(den*(2*rh+zm));positivity
  have hgg : 0<gg := exp_pos _
  have hgg1 : gg ≤ 1 := exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hBl (by linarith))
  have hzEq : zm*gg=z := by
    dsimp [zm,gg,z]
    rw [mul_assoc,←exp_add]
    congr 2
    ring
  have hfEq : fm*gg=c.ul*(c.rmin*2*z/(2*rh+zm))/den := by
    change c.ul*c.rmin*(2*zm)/(den*(2*rh+zm))*gg=_
    rw [show c.ul*c.rmin*(2*zm)/(den*(2*rh+zm))*gg=
      c.ul*(c.rmin*2*(zm*gg)/(2*rh+zm))/den by field_simp [hden.ne',show 2*rh+zm≠0 by positivity] <;> ring,hzEq]
  have hfCount : fm*gg ≤ main s v := by rw [hfEq];exact hfixed.trans hmono
  have hGw : 0 ≤ windowMain vl := by
    have hw:=windowMain_monotone hvl.le
    simpa [windowMain] using hw
  have hBase:=WinnerWarmPade.warm_profile_lower (f:=fm*gg) (by positivity)
    (mul_le_of_le_one_right hfm.le hgg1) hfm hfCount hGw
  have hSoft:=mul_le_mul_of_nonneg_right (softMinReal_le fm (windowMain vl))
    (show 0 ≤ gg by positivity)
  have heq : min fm (windowMain vl)/fm*(fm*gg)=min fm (windowMain vl)*gg := by
    field_simp [hfm.ne']
  rw [heq] at hBase
  have hLast : softMinReal fm (windowMain vl)*gg ≤ witness s v :=
    hSoft.trans (hBase.trans (min_le_min le_rfl (windowMain_monotone hvlv)))
  have hw:=mul_le_mul_of_nonneg_left hLast (exp_pos ((30001/100)*(s-7/8))).le
  convert! hw using 1
  dsimp [warmCell,weighted,gg,fm,vl]
  simp only [c,mul_sub,exp_sub,neg_mul,exp_neg]
  ring

#print axioms warm_cell_lower
end WinnerStrongEnvelope
