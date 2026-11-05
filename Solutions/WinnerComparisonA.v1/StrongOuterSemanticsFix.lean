/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongOuterProgram
import StrongUConsumer
import StrongVConsumer
namespace WinnerStrongOuter
open LeanCert.Core LeanCert.Engine Real
set_option maxHeartbeats 0
@[simp] theorem eval_lit (q : ℚ) (env : ℕ→ℝ) : Expr.eval env (lit q)=(q:ℝ) := rfl
@[simp] theorem eval_add (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (add a b)=Expr.eval env a+Expr.eval env b := rfl
@[simp] theorem eval_mul (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (mul a b)=Expr.eval env a*Expr.eval env b := rfl
@[simp] theorem eval_div (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (dv a b)=Expr.eval env a/Expr.eval env b := rfl
@[simp] theorem eval_sq (a : Expr) (env : ℕ→ℝ) : Expr.eval env (sq a)=(Expr.eval env a)^2 := by simp [sq,pow_two]
@[simp] theorem eval_sub (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (sub a b)=Expr.eval env a-Expr.eval env b := rfl
@[simp] theorem eval_exp (a : Expr) (env : ℕ→ℝ) : Expr.eval env (.exp a)=exp (Expr.eval env a) := rfl
@[simp] theorem eval_pi (env : ℕ→ℝ) : Expr.eval env (.namedConst .pi)=Real.pi := rfl
@[simp] theorem eval_log (a : Expr) (env : ℕ→ℝ) : Expr.eval env (.log a)=log (Expr.eval env a) := rfl
@[simp] theorem h_semantics (env : ℕ→ℝ) : Expr.eval env h=WinnerOldFloors.h := by rfl
 theorem rt_semantics (e : Expr) (env : ℕ→ℝ) (hp : 0<Expr.eval env e) :
    Expr.eval env (rt e)=sqrt (Expr.eval env e) := by
  simp only [rt,eval_exp,eval_div,eval_log,eval_lit]
  rw [sqrt_eq_rpow,rpow_def_of_pos hp]
  norm_num only [Rat.cast_ofNat]
  congr 1
  ring
 theorem mz_semantics (env : ℕ→ℝ) : Expr.eval env mz=WinnerStrongC4Source.mzero := by
  unfold mz
  rw [rt_semantics _ _ (by simp only [eval_add,eval_lit,eval_mul];rw [rt_semantics _ _ (by norm_num)];norm_num;positivity)]
  rw [eval_add,eval_lit,eval_mul,eval_lit,rt_semantics _ _ (by norm_num)]
  norm_num [eval_lit,WinnerStrongC4Source.mzero]

 theorem ulower_semantics (v : Expr) (env : ℕ→ℝ) (hu : 0<WinnerOldFloors.h+Expr.eval env v) :
    Expr.eval env (ulower v)=WinnerStrongC4Source.floorU (Expr.eval env v) := by
  have hm : 0<Expr.eval env (add (dv (lit 6) (sq (.namedConst .pi)))
      (dv (lit (131/125)) (add h v))) := by
    simp only [eval_add,eval_div,eval_sq,eval_pi,eval_lit,h_semantics]
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    positivity
  unfold ulower
  simp only [eval_mul,eval_add,eval_div,eval_sq,eval_lit,eval_exp,mz_semantics,eval_pi,h_semantics,MathConst.toReal]
  rw [rt_semantics _ _ hm,rt_semantics _ _ (by simpa using hu)]
  simp only [eval_mul,eval_add,eval_div,eval_sq,eval_lit,eval_exp,mz_semantics,eval_pi,h_semantics,MathConst.toReal]
  unfold WinnerStrongC4Source.floorU WinnerStrongC4Source.oldC4 WinnerStrongC4Source.oldRzero
    WinnerStrongC4Source.a1 WinnerStrongC4Source.a2 WinnerStrongC4Source.a3 WinnerStrongC4Source.alpha
    WinnerStrongC4Source.mone WinnerOldFloors.ratioFloor WinnerStrongC4.expanded WinnerStrongC4.momentLower
  norm_num only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow]
  simp only [WinnerStrongC4Source.mzero,WinnerStrongC4Source.a1]
  ring_nf

 theorem vlower_semantics (vl vr : Expr) (env : ℕ→ℝ) :
    Expr.eval env (vlower vl vr)=WinnerStrongV.floorV (Expr.eval env vl) (Expr.eval env vr) := by
  unfold vlower
  simp only [eval_mul,eval_add,eval_div,eval_sq,eval_lit,eval_exp,eval_sub,eval_log,mz_semantics,eval_pi,h_semantics,MathConst.toReal]
  have hpRoot : 0<Expr.eval env (dv (.namedConst .pi) (lit (2371/10000))) := by
    rw [eval_div,eval_pi,eval_lit]
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    exact div_pos Real.pi_pos (by norm_num)
  rw [rt_semantics _ _ hpRoot]
  simp only [eval_mul,eval_add,eval_div,eval_sq,eval_lit,eval_exp,eval_sub,eval_log,eval_pi,h_semantics,Expr.eval,MathConst.toReal]
  unfold WinnerStrongV.floorV WinnerStrongV.cFiveLower WinnerStrongV.cSixLower
    WinnerOldC4Source.delta WinnerOldC4Source.alpha
  norm_num only [Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow]
  have hroot : sqrt (Real.pi/(2371/10000:ℝ))=sqrt Real.pi/sqrt (2371/10000:ℝ) := sqrt_div Real.pi_pos.le (2371/10000)
  rw [hroot]
  rfl
#print axioms ulower_semantics
#print axioms vlower_semantics
end WinnerStrongOuter
