/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongOuterSemanticsFix
namespace WinnerStrongC4Source
open Real Set MeasureTheory WinnerOldFloors WinnerStrongC4
set_option maxHeartbeats 0
 theorem ratioFloor_antitone {v vr : ℝ} (hv : 0≤v) (hvr : v≤vr) :
    ratioFloor vr≤ratioFloor v := by
  have hh : 0<h := by linarith [h_lower]
  have hm:=mzero_pos
  unfold ratioFloor
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr
 theorem floorU_antitone {v vr : ℝ} (hv : 0≤v) (hvr : v≤vr) : floorU vr≤floorU v := by
  have hh : 0<h := by linarith [h_lower]
  have hup : 0<h+v := by positivity
  have hurp : 0<h+vr := by linarith
  have hr0:=ratio_nonneg (show 0≤vr by linarith)
  have hz0 : 0≤oldRzero (h+vr) := by unfold oldRzero a2 a1 a3;positivity
  have hprod:=expanded_parameters (j:=momentLower) (fun i _=>moment_lower_nonneg i)
    hup (show h+v≤h+vr by linarith) hr0 (ratioFloor_antitone hv hvr) hz0
    (rzero_antitone hup (by linarith))
  have hnonneg : 0≤expanded momentLower (h+vr) (ratioFloor vr) (oldRzero (h+vr)) := by
    have hh:=expanded_mono (j:=fun _=>0) hurp hr0 hz0 (fun i _=>moment_lower_nonneg i)
    simpa only [expanded,mul_zero,add_zero,zero_add] using hh
  have hc:=c4_antitone hup (show h+v≤h+vr by linarith)
  unfold floorU
  have hp:=mul_le_mul_of_nonneg_left hc (by norm_num [alpha] : 0≤8*alpha)
  exact mul_le_mul hp hprod hnonneg (by unfold alpha oldC4;positivity)
 theorem floorU_sixteen_lower : (1:ℝ)≤floorU 16 := by
  have hc : CH2QRH.DensityComputation.checkUpperBound
      (.neg (WinnerStrongOuter.ulower (.const 16))) 0 0 (-1) WinnerStrongOuter.cfg=true := by native_decide
  have hh:=CH2QRH.DensityComputation.verify_upper _ 0 0 (-1) WinnerStrongOuter.cfg (by decide) hc
  simp only [Finset.Icc_self,Finset.sum_singleton] at hh
  norm_num only [Rat.cast_neg,Rat.cast_one] at hh
  change -LeanCert.Core.Expr.eval (LeanCert.Engine.sumBodyRealEnv 0) (WinnerStrongOuter.ulower (.const 16))≤(-1:ℝ) at hh
  have hs:=WinnerStrongOuter.ulower_semantics (.const 16) (LeanCert.Engine.sumBodyRealEnv 0)
    (by change 0<h+16;linarith [h_lower])
  change _=floorU 16 at hs
  rw [hs] at hh
  linarith
 theorem floorU_lower {v : ℝ} (hv : 0≤v) (hv' : v≤16) : (1:ℝ)≤floorU v :=
  floorU_sixteen_lower.trans (floorU_antitone hv hv')
 theorem floorU_zero_upper : floorU 0≤(2:ℝ) := by
  have hc : CH2QRH.DensityComputation.checkUpperBound
      (WinnerStrongOuter.ulower (.const 0)) 0 0 2 WinnerStrongOuter.cfg=true := by native_decide
  have hh:=CH2QRH.DensityComputation.verify_upper _ 0 0 2 WinnerStrongOuter.cfg (by decide) hc
  simp only [Finset.Icc_self,Finset.sum_singleton] at hh
  norm_num only [Rat.cast_ofNat] at hh
  have hz : LeanCert.Core.Expr.eval (LeanCert.Engine.sumBodyRealEnv 0) (.const 0)=0 := by norm_num [LeanCert.Core.Expr.eval]
  have hs:=WinnerStrongOuter.ulower_semantics (.const 0) (LeanCert.Engine.sumBodyRealEnv 0)
    (by rw [hz];linarith [h_lower])
  rw [hz] at hs
  rw [hs] at hh
  exact hh
 theorem floorU_upper {v : ℝ} (hv : 0≤v) : floorU v≤(2:ℝ) :=
  (floorU_antitone (by norm_num) hv).trans floorU_zero_upper
#print axioms floorU_lower
end WinnerStrongC4Source
