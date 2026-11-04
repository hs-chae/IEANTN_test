/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldC4Source
import ReferenceVLower
import Mathlib.Analysis.Complex.ExponentialBounds
namespace WinnerOldC4Source
open Real Set MeasureTheory
open WinnerOldFloors WinnerOriginalScalars.Reference
set_option maxHeartbeats 0
noncomputable def delta : ℝ := 3599/10000
noncomputable def cfive (u : ℝ) : ℝ :=
  Real.pi*mzero*(529/1000)/(2*delta)*(1+2*delta/u)^2*
    exp (2*delta*eulerMascheroniConstant/u)
noncomputable def csix (u : ℝ) : ℝ :=
  (529/1000)/(5*delta*exp delta)*(1+delta/u)^2*
    exp (delta*(eulerMascheroniConstant-log 5)/u)+(121/200)*exp (-2*delta)/u^2
noncomputable def oldV (u : ℝ) : ℝ :=
  exp (2*alpha*((1+delta/u)/exp u)^2)*
    (2*cfive u+2*csix u*Real.pi*mzero*exp (-u)+sqrt Real.pi/sqrt (2*alpha)*csix u)

theorem cfive_nonneg {u : ℝ} (hu : 0<u) : 0≤cfive u := by
  have hm:=mzero_pos
  unfold cfive delta
  positivity
theorem csix_nonneg {u : ℝ} (hu : 0<u) : 0≤csix u := by unfold csix delta;positivity

theorem cfive_floor {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) :
    sourceCFiveFloor v≤cfive u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have humax : 0<h+v := by positivity
  have hm:=mzero_pos
  have hg : (1/2:ℝ)≤eulerMascheroniConstant := one_half_lt_eulerMascheroniConstant.le
  have hpoly : 1+2*delta/(h+v)≤1+2*delta/u := by unfold delta;gcongr
  have hexp : delta/(h+v)≤2*delta*eulerMascheroniConstant/u := by
    calc delta/(h+v) ≤ delta/u := by unfold delta;gcongr
         _ ≤ _ := div_le_div_of_nonneg_right (by unfold delta at *;nlinarith) hup.le
  unfold sourceCFiveFloor cfive
  change Real.pi*mzero*(529/1000)/(2*delta)*(1+2*delta/(h+v))^2*exp (delta/(h+v))≤_
  gcongr
  all_goals unfold delta; positivity

theorem csix_floor {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) :
    sourceCSixFloor v≤csix u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have humax : 0<h+v := by positivity
  have hg : (1/2:ℝ)≤eulerMascheroniConstant := one_half_lt_eulerMascheroniConstant.le
  have hlog : (1:ℝ)<log 5 := (lt_log_iff_exp_lt (by norm_num)).mpr
    (exp_one_lt_three.trans (by norm_num))
  have hneg : delta*((1/2:ℝ)-log 5)≤0 := by unfold delta;nlinarith
  have hexp : delta*((1/2:ℝ)-log 5)/h≤delta*(eulerMascheroniConstant-log 5)/u := by
    calc delta*((1/2:ℝ)-log 5)/h ≤ delta*((1/2:ℝ)-log 5)/u := by
           apply (div_le_div_iff₀ hh hup).mpr
           exact mul_le_mul_of_nonpos_left hlu hneg
         _ ≤ _ := div_le_div_of_nonneg_right (by unfold delta at *;nlinarith) hup.le
  have hpoly : 1+delta/(h+v)≤1+delta/u := by unfold delta;gcongr
  have hpow : u^2≤(h+v)^2 := pow_le_pow_left₀ hup.le hur 2
  unfold sourceCSixFloor csix
  change (529/1000)/(5*delta*exp delta)*(1+delta/(h+v))^2*
    exp (delta*((1/2:ℝ)-log 5)/h)+(121/200)*exp (-2*delta)/(h+v)^2≤_
  gcongr
  all_goals unfold delta; positivity

theorem oldV_floor {u v : ℝ} (hv : 0≤v) (hlu : h≤u) (hur : u≤h+v) :
    sourceVFloor v≤oldV u := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<u := hh.trans_le hlu
  have hm:=mzero_pos
  have hc5:=cfive_nonneg hup
  have hc6:=csix_nonneg hup
  have h1:=cfive_floor hv hlu hur
  have h2:=csix_floor hv hlu hur
  have hexp : 1≤exp (2*alpha*((1+delta/u)/exp u)^2) := by
    apply one_le_exp
    unfold alpha
    positivity
  have hcoef : 0≤sqrt Real.pi/sqrt (2*alpha) := by unfold alpha;positivity
  have hterm : 0≤2*csix u*Real.pi*mzero*exp (-u) := by positivity
  unfold sourceVFloor oldV
  change 2*sourceCFiveFloor v+sqrt Real.pi/sqrt (2*alpha)*sourceCSixFloor v≤_
  have hbase : 2*sourceCFiveFloor v+sqrt Real.pi/sqrt (2*alpha)*sourceCSixFloor v≤
      2*cfive u+2*csix u*Real.pi*mzero*exp (-u)+sqrt Real.pi/sqrt (2*alpha)*csix u := by
    have hh2:=mul_le_mul_of_nonneg_left h2 hcoef
    linarith
  apply hbase.trans
  have hpos : 0≤2*cfive u+2*csix u*Real.pi*mzero*exp (-u)+sqrt Real.pi/sqrt (2*alpha)*csix u := by positivity
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hpos

#print axioms oldV_floor
end WinnerOldC4Source
