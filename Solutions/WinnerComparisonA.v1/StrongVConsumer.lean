/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongGamma
import OldVSource
namespace WinnerStrongV
open Real Set MeasureTheory WinnerOldFloors
open WinnerOldC4Source
set_option maxHeartbeats 0
noncomputable def cFiveLower (vr : ℝ) : ℝ :=
  Real.pi*WinnerOldC4Source.mzero*(529/1000)/(2*delta)*(1+2*delta/(h+vr))^2*
    exp (2*delta*(577/1000)/(h+vr))
noncomputable def cSixLower (vl vr : ℝ) : ℝ :=
  (529/1000)/(5*delta*exp delta)*(1+delta/(h+vr))^2*
    exp (delta*((577/1000)-log 5)/(h+vl))+(121/200)*exp (-2*delta)/(h+vr)^2
noncomputable def floorV (vl vr : ℝ) : ℝ :=
  2*cFiveLower vr+sqrt Real.pi/sqrt (2*alpha)*cSixLower vl vr

theorem cfive_lower {u vr : ℝ} (hvr : 0≤vr) (hu : h≤u) (hur : u≤h+vr) :
    cFiveLower vr≤cfive u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hu
  have humax : 0<h+vr := by positivity
  have hm:=mzero_pos
  have hg:=WinnerStrongC4.gamma_lower
  have hexp : 2*delta*(577/1000)/(h+vr)≤2*delta*eulerMascheroniConstant/u := by
    calc _≤2*delta*(577/1000)/u := by unfold delta;gcongr
         _≤_ := div_le_div_of_nonneg_right (by unfold delta at *;nlinarith) hup.le
  unfold cFiveLower cfive
  gcongr
  all_goals unfold delta;positivity

theorem csix_lower {u vl vr : ℝ} (hvl : 0≤vl) (hlr : vl≤vr)
    (hlu : h+vl≤u) (hur : u≤h+vr) : cSixLower vl vr≤csix u := by
  have hh : 0<h := by linarith [h_lower]
  have hmin : 0<h+vl := by positivity
  have hup : 0<u := hmin.trans_le hlu
  have humax : 0<h+vr := hup.trans_le hur
  have hg:=WinnerStrongC4.gamma_lower
  have hlog : (1:ℝ)<log 5 := (lt_log_iff_exp_lt (by norm_num)).mpr
    (exp_one_lt_three.trans (by norm_num))
  have hneg : delta*((577/1000)-log 5)≤0 := by unfold delta;nlinarith
  have hexp : delta*((577/1000)-log 5)/(h+vl)≤delta*(eulerMascheroniConstant-log 5)/u := by
    calc _≤delta*((577/1000)-log 5)/u := by
           apply (div_le_div_iff₀ hmin hup).mpr
           exact mul_le_mul_of_nonpos_left hlu hneg
         _≤_ := div_le_div_of_nonneg_right (by unfold delta at *;nlinarith) hup.le
  have hpow : u^2≤(h+vr)^2 := pow_le_pow_left₀ hup.le hur 2
  unfold cSixLower csix
  gcongr
  all_goals unfold delta;positivity

theorem oldV_floor {u vl vr : ℝ} (hvl : 0≤vl) (hlr : vl≤vr)
    (hlu : h+vl≤u) (hur : u≤h+vr) : floorV vl vr≤oldV u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := lt_of_lt_of_le (by positivity : 0<h+vl) hlu
  have hm:=mzero_pos
  have hc5:=cfive_nonneg hup
  have hc6:=csix_nonneg hup
  have h1:=cfive_lower (hvl.trans hlr) (by linarith) hur
  have h2:=csix_lower hvl hlr hlu hur
  have hexp : 1≤exp (2*alpha*((1+delta/u)/exp u)^2) := by
    apply one_le_exp
    unfold alpha
    positivity
  have hcoef : 0≤sqrt Real.pi/sqrt (2*alpha) := by unfold alpha;positivity
  have hterm : 0≤2*csix u*Real.pi*WinnerOldC4Source.mzero*exp (-u) := by positivity
  unfold floorV oldV
  have hbase : 2*cFiveLower vr+sqrt Real.pi/sqrt (2*alpha)*cSixLower vl vr≤
      2*cfive u+2*csix u*Real.pi*WinnerOldC4Source.mzero*exp (-u)+sqrt Real.pi/sqrt (2*alpha)*csix u := by
    have hh2:=mul_le_mul_of_nonneg_left h2 hcoef
    linarith
  apply hbase.trans
  have hpos : 0≤2*cfive u+2*csix u*Real.pi*WinnerOldC4Source.mzero*exp (-u)+sqrt Real.pi/sqrt (2*alpha)*csix u := by positivity
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hpos

#print axioms oldV_floor
end WinnerStrongV
