/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongEnvelope
import StrongVCap
import ArbitraryOuterAssembly
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors WinnerOldC4Source WinnerOldOuter.Assembly
set_option maxHeartbeats 0
noncomputable def data (v0 step : ℝ) (k : ℕ) : CellData :=
  let vl:=v0+step*k
  let vr:=vl+step
  rowData v0 step (WinnerStrongC4Source.floorU vr) (WinnerStrongV.floorV vl vr) k
 theorem data_Bl_nonneg {v0 step : ℝ} {k : ℕ}
    (hv0 : 0≤v0) (hstep : 0≤step) (hmax : v0+step*(k+1)≤16) : 0≤(data v0 step k).Bl := by
  let vl:=v0+step*k
  let vr:=vl+step
  have hvl : 0≤vl := by dsimp [vl];positivity
  have hvr : 0≤vr := by dsimp [vr];positivity
  have hvr16 : vr≤16 := by dsimp [vr,vl];push_cast at hmax ⊢;linarith
  let U:=WinnerStrongC4Source.floorU vr
  let V:=WinnerStrongV.floorV vl vr
  have hU : (1:ℝ)≤U := WinnerStrongC4Source.floorU_lower hvr hvr16
  have hV : 0<V := WinnerStrongV.floorV_positive hvl hvr
  have hV' : V≤8 := WinnerStrongV.floorV_upper hvl hvr
  have hleft:=WinnerStrongBounds.leftD_pos hU hV hV' (show h≤h+vl by linarith)
  have hden : 0<h+vr+2*delta := by have hh:=h_lower;unfold delta;linarith
  have ha : 0≤aSlope (h+vr) := by
    unfold aSlope
    have hr : 4*delta/(h+vr+2*delta)≤2 := (div_le_iff₀ hden).mpr (by unfold delta;linarith [h_lower])
    linarith
  convert! mul_nonneg ha hleft.le using 1
  dsimp [data,rowData,U,V,vl,vr,leftD,aSlope,delta,WinnerOldFloors.h]
  norm_num

 theorem main_cell_lower {v0 step width s v : ℝ} {k : ℕ}
    (hv0 : 0<v0) (hstep : 0≤step) (hmax : v0+step*(k+1)≤16)
    (hwidth : 0≤width) (hs0 : (3/4:ℝ)≤s) (hs1 : s≤7/8) (hs2 : 7/8-width≤s)
    (hvlv : v0+step*k≤v) (hvvr : v≤v0+step*(k+1))
    (hcap : (data v0 step k).ul*(data v0 step k).zl*
      exp ((data v0 step k).Bl*width)/((3663/5000)*Real.pi)≤windowMain (v0+step*k)) :
    WinnerOldOuter.Arbitrary.cellProfile (30001/100) (7/8) ((3663/5000)*Real.pi)
      (data v0 step k) s≤weighted s v := by
  let vl:=v0+step*k
  let vr:=vl+step
  let U:=WinnerStrongC4Source.floorU vr
  let V:=WinnerStrongV.floorV vl vr
  let c:=data v0 step k
  let zl:=c.zl*exp (c.Bl*(7/8-s))
  let zu:=c.zu*exp (c.Bu*(7/8-s))
  let den:ℝ:=(3663/5000)*Real.pi
  have hden : 0<den := by dsimp [den];positivity
  have hvl : 0<vl := by dsimp [vl];positivity
  have hvr : 0<vr := by dsimp [vr];positivity
  have hvr16 : vr≤16 := by dsimp [vr,vl];push_cast at hmax ⊢;linarith
  have hvlv' : vl≤v := hvlv
  have hvvr' : v≤vr := by dsimp [vr,vl];push_cast at hvvr ⊢;linarith
  have hvp : 0≤v := hvl.le.trans hvlv'
  have hU : (1:ℝ)≤U := WinnerStrongC4Source.floorU_lower hvr.le hvr16
  have hUp : 0<U := by linarith
  have hV : 0<V := WinnerStrongV.floorV_positive hvl.le hvr.le
  have hV8 : V≤8 := WinnerStrongV.floorV_upper hvl.le hvr.le
  have hcz:=WinnerStrongBounds.cell_z_bounds hv0.le hstep hU hV hV8 hs0 hs1 hvlv hvvr
  change zl≤zModel U V s (h+v) ∧ zModel U V s (h+v)≤zu at hcz
  have hul : 0≤c.ul := by change 0≤h+vl;linarith [h_lower]
  have hur : 0≤c.ur := by change 0≤h+vr;linarith [h_lower]
  have hlu : c.ul≤h+v := by change h+vl≤h+v;linarith
  have hru : h+v≤c.ur := by change h+v≤h+vr;linarith
  have hrmin : 0<c.rmin := by
    dsimp [c,data,rowData]
    have he : exp (-vl)<1 := exp_lt_one_iff.mpr (by linarith)
    change 0<1-exp (-vl)
    linarith
  have hratio : c.rmin≤heightRatio v := by
    have he : exp (-v)≤exp (-vl) := exp_le_exp.mpr (by linarith)
    dsimp [c,data,rowData,heightRatio]
    linarith [exp_pos (-(h+v))]
  have hzl : 0≤zl := by dsimp [zl,c,data,rowData];positivity
  have hraw:=WinnerOldAnalytic.count_cell_lower hul hlu hru hrmin hratio hzl hcz.1 hcz.2
  have hcount : (c.ul*zl-c.ur*zu^2/(2*c.rmin))/den≤countModel U V s v := by
    have hd:=div_le_div_of_nonneg_right hraw hden.le
    convert! hd using 1
    unfold countModel
    dsimp [den]
    unfold d
    ring
  have hUf : U≤WinnerStrongC4Source.oldU (h+v) :=
    WinnerStrongC4Source.oldU_floor hvr.le (show h≤h+v by linarith) (by linarith)
  have hVf : V≤WinnerOldC4Source.oldV (h+v) :=
    WinnerStrongV.oldV_floor hvl.le (by dsimp [vr];linarith) (by linarith) (by linarith)
  have hmono:=countModel_mono hUp hV hUf hVf hs0 hs1 hvp
  have hmain : (c.ul*zl-c.ur*zu^2/(2*c.rmin))/den≤main s v := hcount.trans hmono
  have hBl:=data_Bl_nonneg hv0.le hstep hmax
  have hexp : exp (c.Bl*(7/8-s))≤exp (c.Bl*width) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hBl)
  have hzlcoef : 0≤c.zl := by dsimp [c,data,rowData];positivity
  have hpos : c.ul*zl/den≤c.ul*c.zl*exp (c.Bl*width)/den := by
    have hh:=div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hzlcoef) hul) hden.le
    convert! hh using 1 <;> (try dsimp only [zl]) <;> ring
  have hcorr : 0≤c.ur*zu^2/(2*c.rmin) := by positivity
  have hdrop : (c.ul*zl-c.ur*zu^2/(2*c.rmin))/den≤c.ul*zl/den :=
    div_le_div_of_nonneg_right (by linarith) hden.le
  have hwindow : (c.ul*zl-c.ur*zu^2/(2*c.rmin))/den≤windowMain v :=
    hdrop.trans (hpos.trans (hcap.trans (windowMain_monotone hvlv)))
  have hmin : (c.ul*zl-c.ur*zu^2/(2*c.rmin))/den≤witness s v := le_min hmain hwindow
  have hw:=mul_le_mul_of_nonneg_left hmin (exp_pos ((30001/100)*(s-7/8))).le
  convert! hw using 1
  dsimp [WinnerOldOuter.Arbitrary.cellProfile,weighted,c,zl,zu,den]
  ring
#print axioms main_cell_lower
end WinnerStrongEnvelope
