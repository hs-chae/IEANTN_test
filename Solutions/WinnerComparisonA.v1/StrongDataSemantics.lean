/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongCell
import StrongOuterSemanticsFix
namespace WinnerStrongOuter
open LeanCert.Core LeanCert.Engine Real WinnerOldFloors WinnerOldOuter.Assembly
set_option maxHeartbeats 0
@[simp] theorem eval_neg (e : Expr) (env : ℕ→ℝ) : Expr.eval env (.neg e)= -Expr.eval env e := rfl
noncomputable def evalData (c : Bounds) (env : ℕ→ℝ) : CellData :=
  ⟨Expr.eval env c.ul,Expr.eval env c.ur,Expr.eval env c.zl,Expr.eval env c.zu,
    Expr.eval env c.bl,Expr.eval env c.bu,Expr.eval env c.rmin⟩
 theorem boundsData_semantics (vl vr : Expr) (env : ℕ→ℝ) (hu : 0<WinnerOldFloors.h+Expr.eval env vr) :
    evalData (bounds vl vr) env=rowData (Expr.eval env vl) (Expr.eval env vr-Expr.eval env vl)
      (WinnerStrongC4Source.floorU (Expr.eval env vr))
      (WinnerStrongV.floorV (Expr.eval env vl) (Expr.eval env vr)) 0 := by
  have hU:=ulower_semantics vr env hu
  have hV:=vlower_semantics vl vr env
  unfold evalData
  simp only [rowData,Nat.cast_zero,mul_zero,add_zero,add_sub_cancel]
  congr 1
  all_goals
    simp only [evalData,bounds,rowData,Id.run_pure,eval_lit,eval_add,eval_mul,eval_div,eval_sq,
      eval_sub,eval_neg,eval_log,eval_exp,eval_pi,h_semantics,hU,hV,Nat.cast_zero,
      mul_zero,add_zero,add_sub_cancel]
  all_goals norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_mul]
  all_goals try simp only [WinnerOldFloors.h,add_comm,add_left_comm,add_assoc]
  all_goals first | rfl | (congr 1 <;> first |rfl|ring) |ring
 theorem data_row_between (v0 step : ℝ) (k : ℕ) :
    rowData (v0+step*k) step (WinnerStrongC4Source.floorU (v0+step*k+step))
      (WinnerStrongV.floorV (v0+step*k) (v0+step*k+step)) 0=WinnerStrongEnvelope.data v0 step k := by
  unfold WinnerStrongEnvelope.data rowData
  simp only [Nat.cast_zero,mul_zero,add_zero]

 theorem bounds_window_semantics (vl vr : Expr) (env : ℕ→ℝ) :
    Expr.eval env (bounds vl vr).window=WinnerOldC4Source.windowMain (Expr.eval env vl) := by
  simp only [bounds,Id.run_pure,WinnerOldC4Source.windowMain,eval_lit,eval_add,eval_mul,eval_div,
    eval_sq,eval_sub,eval_neg,eval_log,eval_exp,eval_pi,h_semantics]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]

#print axioms boundsData_semantics
end WinnerStrongOuter
