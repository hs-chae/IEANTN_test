/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongCell
namespace WinnerStrongEnvelope
open Real Set MeasureTheory WinnerOldFloors WinnerOldC4Source WinnerOldOuter.Assembly
set_option maxHeartbeats 0
 theorem floorV_one_lower {vl vr : ℝ} (hvl : 0 ≤ vl) (hvr : 0 ≤ vr) : (1:ℝ) ≤ WinnerStrongV.floorV vl vr := by
  have hh : 0<h := by linarith [h_lower]
  have hu : 0<h+vr := by positivity
  have huL : 0<h+vl := by positivity
  have hm : (1:ℝ) ≤ WinnerOldC4Source.mzero := by
    unfold WinnerOldC4Source.mzero
    rw [one_le_sqrt]
    nlinarith [sqrt_nonneg (6/5:ℝ)]
  have hbase : (1:ℝ) ≤ Real.pi*WinnerOldC4Source.mzero*(529/1000)/(2*delta) := by
    apply (le_div_iff₀ (by norm_num [delta] : 0<2*delta)).mpr
    have hp:=mul_le_mul pi_gt_three.le hm (by norm_num) Real.pi_pos.le
    unfold delta
    nlinarith
  have hpoly : (1:ℝ) ≤ (1+2*delta/(h+vr))^2 := by
    have hr : 0 ≤ 2*delta/(h+vr) := by unfold delta;positivity
    nlinarith
  have he : (1:ℝ) ≤ exp (2*delta*(577/1000)/(h+vr)) := by
    apply one_le_exp
    unfold delta
    positivity
  have hc5 : (1:ℝ) ≤ WinnerStrongV.cFiveLower vr := by
    unfold WinnerStrongV.cFiveLower
    have hbase0 : 0 ≤ Real.pi*WinnerOldC4Source.mzero*(529/1000)/(2*delta) := by linarith
    have hp:=mul_le_mul hbase hpoly (by norm_num) hbase0
    have hprod0 : 0 ≤ Real.pi*WinnerOldC4Source.mzero*(529/1000)/(2*delta)*(1+2*delta/(h+vr))^2 := by nlinarith
    have hpp:=mul_le_mul hp he (by norm_num) hprod0
    simpa only [one_mul] using hpp
  have hc6 : 0 ≤ WinnerStrongV.cSixLower vl vr := by unfold WinnerStrongV.cSixLower WinnerOldC4Source.delta;positivity
  have hroot : 0 ≤ sqrt Real.pi/sqrt (2*alpha) := by unfold alpha;positivity
  unfold WinnerStrongV.floorV
  linarith [mul_nonneg hroot hc6]
 theorem log_at_most_five {u : ℝ} (hu : 0<u) (hu45 : u ≤ 45) : log u ≤ 5 := by
  have he : (45:ℝ) ≤ exp 5 := by
    have he : (5/2:ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
    have hp:=pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/2) he 5
    rw [←exp_nat_mul] at hp
    norm_num at hp ⊢
    linarith
  exact (log_le_iff_le_exp hu).mpr (hu45.trans he)
 theorem aSlope_bounds {u : ℝ} (hu : 0<u) : 0 ≤ aSlope u ∧ aSlope u ≤ 2 := by
  have hd : 0<delta := by norm_num [delta]
  have hden : 0<u+2*delta := by positivity
  have hf0 : 0 ≤ 4*delta/(u+2*delta) := by positivity
  have hf2 : 4*delta/(u+2*delta) ≤ 2 := (div_le_iff₀ hden).mpr (by nlinarith)
  unfold aSlope
  exact ⟨by linarith,by linarith⟩
 theorem leftD_upper {U V u : ℝ} (hU : 0<U) (hU2 : U ≤ 2) (hV : 1 ≤ V)
    (hu : 0<u) (hu45 : u ≤ 45) : leftD U V u ≤ 66 := by
  have hVp : 0<V := by linarith
  have hrat : 0<U/V := div_pos hU hVp
  have hrat2 : U/V ≤ 2 := (div_le_iff₀ hVp).mpr (by nlinarith)
  have hlog:=log_le_sub_one_of_pos hrat
  have hlog5:=log_at_most_five hu hu45
  unfold leftD
  nlinarith
 theorem data_slopes_upper {v0 step : ℝ} {k : ℕ}
    (hv0 : 0 ≤ v0) (hs : 0 ≤ step) (hmax : v0+step*(k+1) ≤ 16) :
    (data v0 step k).Bl ≤ 132 ∧ (data v0 step k).Bu ≤ 132 := by
  let vl:=v0+step*k
  let vr:=vl+step
  have hvl : 0 ≤ vl := by dsimp [vl];positivity
  have hvr : 0 ≤ vr := by dsimp [vr];positivity
  have hvr16 : vr ≤ 16 := by dsimp [vr,vl];push_cast at hmax ⊢;linarith
  have hvl16 : vl ≤ 16 := by dsimp [vr] at hvr16;linarith
  have hh : h ≤ 29 := height_log_bounds.2
  have hlp : 0<h+vl := by linarith [h_lower]
  have hrp : 0<h+vr := by linarith [h_lower]
  have hl45 : h+vl ≤ 45 := by linarith
  have hr45 : h+vr ≤ 45 := by linarith
  let U:=WinnerStrongC4Source.floorU vr
  let V:=WinnerStrongV.floorV vl vr
  have hU1 : (1:ℝ) ≤ U := WinnerStrongC4Source.floorU_lower hvr hvr16
  have hU : 0<U := by linarith
  have hU2 : U ≤ 2 := WinnerStrongC4Source.floorU_upper hvr
  have hV : (1:ℝ) ≤ V := floorV_one_lower hvl hvr
  have hVp : 0<V := by linarith
  have hV8 : V ≤ 8 := WinnerStrongV.floorV_upper hvl hvr
  have hDL:=WinnerStrongBounds.leftD_pos hU1 hVp hV8 (show h ≤ h+vl by linarith)
  have hDR:=WinnerStrongBounds.leftD_pos hU1 hVp hV8 (show h ≤ h+vr by linarith)
  have hDUl:=leftD_upper hU hU2 hV hlp hl45
  have hDUr:=leftD_upper hU hU2 hV hrp hr45
  have hAl:=aSlope_bounds hlp
  have hAr:=aSlope_bounds hrp
  have hleft : aSlope (h+vr)*leftD U V (h+vl) ≤ 132 := by
    have hp:=mul_le_mul_of_nonneg_right hAr.2 hDL.le
    nlinarith
  have hright : aSlope (h+vl)*leftD U V (h+vr) ≤ 132 := by
    have hp:=mul_le_mul_of_nonneg_right hAl.2 hDR.le
    nlinarith
  constructor
  · convert! hleft using 1
    dsimp [data,rowData,U,V,vl,vr,aSlope,leftD,delta,WinnerOldFloors.h]
    norm_num
  · convert! hright using 1
    dsimp [data,rowData,U,V,vl,vr,aSlope,leftD,delta,WinnerOldFloors.h]
    norm_num
 theorem data_exponents_ne {v0 step : ℝ} {k : ℕ}
    (hv0 : 0 ≤ v0) (hs : 0 ≤ step) (hmax : v0+step*(k+1) ≤ 16) :
    (30001/100:ℝ)-(data v0 step k).Bl≠0 ∧
    (30001/100:ℝ)-2*(data v0 step k).Bu≠0 := by
  have hb:=data_slopes_upper hv0 hs hmax
  constructor <;> linarith [hb.1,hb.2]
#print axioms data_exponents_ne
end WinnerStrongEnvelope
