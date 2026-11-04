/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongOuterSemanticsFix
import OriginalScalars
namespace WinnerStrongV
open Real LeanCert.Core
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def cfiveExpr : Expr :=
  let p:=Expr.namedConst .pi
  let d:=Expr.const (3599/10000)
  let h:=WinnerStrongOuter.h
  let z:=WinnerStrongOuter.mz
  WinnerStrongOuter.mul
    (WinnerStrongOuter.mul
      (WinnerStrongOuter.dv (WinnerStrongOuter.mul (WinnerStrongOuter.mul p z) (.const (529/1000)))
        (WinnerStrongOuter.mul (.const 2) d))
      (WinnerStrongOuter.sq (WinnerStrongOuter.add (.const 1)
        (WinnerStrongOuter.dv (WinnerStrongOuter.mul (.const 2) d) h))))
    (.exp (WinnerStrongOuter.dv
      (WinnerStrongOuter.mul (WinnerStrongOuter.mul (.const 2) d) (.const (577/1000))) h))

theorem cfive_expr_semantics : WinnerOriginalScalars.value cfiveExpr=cFiveLower 0 := by
  unfold cfiveExpr WinnerOriginalScalars.value
  simp only [WinnerStrongOuter.eval_mul,WinnerStrongOuter.eval_div,WinnerStrongOuter.eval_add,
    WinnerStrongOuter.eval_sq,WinnerStrongOuter.eval_lit,WinnerStrongOuter.eval_pi,
    WinnerStrongOuter.eval_exp,WinnerStrongOuter.mz_semantics,WinnerStrongOuter.h_semantics]
  unfold cFiveLower WinnerOldC4Source.delta WinnerOldC4Source.mzero WinnerStrongC4Source.mzero
  norm_num only [Rat.cast_div,Rat.cast_ofNat,add_zero]

theorem cfive_zero_upper : cFiveLower 0 ≤ 27/8 := by
  rw [←cfive_expr_semantics]
  have h:=WinnerOriginalScalars.closed_upper cfiveExpr (27/8) (by native_decide)
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  exact h

theorem cfive_anchor_upper {vr:ℝ} (hvr:0 ≤ vr) : cFiveLower vr ≤ 27/8 := by
  have hh:0<WinnerOldFloors.h := by linarith [WinnerOldFloors.h_lower]
  have hd:0<WinnerOldC4Source.delta := by norm_num [WinnerOldC4Source.delta]
  have hm:=WinnerOldC4Source.mzero_pos
  apply le_trans _ cfive_zero_upper
  unfold cFiveLower
  simp only [add_zero]
  gcongr <;> linarith

theorem csix_anchor_upper {vl vr:ℝ} (hvl:0 ≤ vl) (hvr:0 ≤ vr) : cSixLower vl vr ≤ 1/4 := by
  have hh:0<WinnerOldFloors.h := by linarith [WinnerOldFloors.h_lower]
  have hl:(28:ℝ) ≤ WinnerOldFloors.h+vr := by linarith [WinnerOldFloors.h_lower]
  have hleft:0<WinnerOldFloors.h+vl := by positivity
  have hright:0<WinnerOldFloors.h+vr := by positivity
  have hd:0<WinnerOldC4Source.delta := by norm_num [WinnerOldC4Source.delta]
  have hlog:(1:ℝ)<log 5 := (lt_log_iff_exp_lt (by norm_num)).mpr
    (exp_one_lt_three.trans (by norm_num))
  have hn:exp (WinnerOldC4Source.delta*((577/1000)-log 5)/(WinnerOldFloors.h+vl)) ≤ 1 := by
    apply exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ hleft.le
    unfold WinnerOldC4Source.delta
    nlinarith
  have he:=add_one_le_exp WinnerOldC4Source.delta
  have hfirst :
      (529/1000:ℝ)/(5*WinnerOldC4Source.delta*exp WinnerOldC4Source.delta)*
        (1+WinnerOldC4Source.delta/(WinnerOldFloors.h+vr))^2 ≤
      (529/1000:ℝ)/(5*WinnerOldC4Source.delta*(1+WinnerOldC4Source.delta))*
        (1+WinnerOldC4Source.delta/28)^2 := by
    gcongr <;> linarith
  have hsecond : (121/200:ℝ)*exp (-2*WinnerOldC4Source.delta)/(WinnerOldFloors.h+vr)^2 ≤
      (121/200:ℝ)/(28:ℝ)^2 := by
    have he':exp (-2*WinnerOldC4Source.delta) ≤ 1 := exp_le_one_iff.mpr (by linarith)
    calc _ ≤ (121/200:ℝ)*1/(28:ℝ)^2 := by gcongr
         _ = _ := by ring
  have hpos : 0 ≤ (529/1000:ℝ)/(5*WinnerOldC4Source.delta*exp WinnerOldC4Source.delta)*
      (1+WinnerOldC4Source.delta/(WinnerOldFloors.h+vr))^2 := by positivity
  have hprod:=mul_le_mul_of_nonneg_left hn hpos
  unfold cSixLower
  norm_num [WinnerOldC4Source.delta] at hfirst hsecond hprod ⊢
  nlinarith

theorem root_coefficient_upper : sqrt Real.pi/sqrt (2*WinnerOldC4Source.alpha) ≤ 5 := by
  have hd:0<2*WinnerOldC4Source.alpha := by norm_num [WinnerOldC4Source.alpha]
  rw [←sqrt_div Real.pi_pos.le]
  apply (sqrt_le_iff).mpr
  constructor
  · norm_num
  · apply (div_le_iff₀ hd).mpr
    norm_num [WinnerOldC4Source.alpha]
    linarith [Real.pi_lt_four]

theorem floorV_positive {vl vr:ℝ} (hvl:0 ≤ vl) (hvr:0 ≤ vr) : 0<floorV vl vr := by
  have hh:0<WinnerOldFloors.h := by linarith [WinnerOldFloors.h_lower]
  have hl:0<WinnerOldFloors.h+vl := by positivity
  have hr:0<WinnerOldFloors.h+vr := by positivity
  have hm:=WinnerOldC4Source.mzero_pos
  unfold floorV cFiveLower cSixLower WinnerOldC4Source.delta WinnerOldC4Source.alpha
  positivity

theorem floorV_upper {vl vr:ℝ} (hvl:0 ≤ vl) (hvr:0 ≤ vr) : floorV vl vr ≤ 8 := by
  have h5:=cfive_anchor_upper hvr
  have h6:=csix_anchor_upper hvl hvr
  have hc:=root_coefficient_upper
  have hd:0<WinnerOldC4Source.delta := by norm_num [WinnerOldC4Source.delta]
  have hn:0 ≤ cSixLower vl vr := by unfold cSixLower;positivity
  have hprod:=mul_le_mul hc h6 hn (by norm_num : (0:ℝ) ≤ 5)
  unfold floorV
  nlinarith

#print axioms floorV_positive
#print axioms floorV_upper
end WinnerStrongV
