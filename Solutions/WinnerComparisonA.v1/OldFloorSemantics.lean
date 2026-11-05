/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldFloorProgram
import OldAnalytic
namespace WinnerOldFloors
open LeanCert.Core LeanCert.Engine Real Set MeasureTheory
set_option maxHeartbeats 0

noncomputable def h : ℝ := log 3000000000000
noncomputable def c4Floor (v : ℝ) : ℝ :=
  (611/1000:ℝ)^2*(sqrt (6/Real.pi^2+(131/125)/(h+v))+
    1/((1461/1000)*sqrt (h+v)))^2
noncomputable def ratioFloor (v : ℝ) : ℝ :=
  Real.pi*sqrt (1+(2/3)*sqrt (6/5))*(31/50)/(6/Real.pi^2*(h+v)+131/125)

@[simp] theorem eval_lit (q : ℚ) (env : ℕ→ℝ) : Expr.eval env (lit q)=(q:ℝ) := rfl
@[simp] theorem eval_add (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (add a b)=Expr.eval env a+Expr.eval env b := rfl
@[simp] theorem eval_mul (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (mul a b)=Expr.eval env a*Expr.eval env b := rfl
@[simp] theorem eval_div (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (dv a b)=Expr.eval env a/Expr.eval env b := rfl
@[simp] theorem eval_sq (a : Expr) (env : ℕ→ℝ) : Expr.eval env (sq a)=(Expr.eval env a)^2 := by simp [sq,pow_two]
@[simp] theorem eval_sub (a b : Expr) (env : ℕ→ℝ) : Expr.eval env (sub a b)=Expr.eval env a-Expr.eval env b := by rfl
@[simp] theorem eval_exp (a : Expr) (env : ℕ→ℝ) : Expr.eval env (.exp a)=exp (Expr.eval env a) := rfl
@[simp] theorem eval_pi (env : ℕ→ℝ) : Expr.eval env (.namedConst .pi)=Real.pi := rfl

 theorem rt_semantics (e : Expr) (env : ℕ→ℝ) (hp : 0<Expr.eval env e) :
    Expr.eval env (rt e)=sqrt (Expr.eval env e) := by
  simp only [rt,eval_exp,eval_div,Expr.eval,eval_lit]
  rw [sqrt_eq_rpow,rpow_def_of_pos hp]
  norm_num only [Rat.cast_ofNat]
  congr 1
  ring

 @[simp] theorem h_semantics (env : ℕ→ℝ) : Expr.eval env hExpr=h := by norm_num [hExpr,Expr.eval,h]

 theorem mzero_semantics (env : ℕ→ℝ) :
    Expr.eval env mzero=sqrt (1+(2/3)*sqrt (6/5)) := by
  have hi := rt_semantics (lit (6/5)) env (by norm_num [eval_lit])
  norm_num only [eval_lit,Rat.cast_div,Rat.cast_ofNat] at hi
  have hp : 0<Expr.eval env (add (lit 1) (mul (lit (2/3)) (rt (lit (6/5))))) := by
    simp only [eval_add,eval_mul,eval_lit,hi]
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    positivity
  unfold mzero
  rw [rt_semantics _ _ hp]
  simp only [eval_add,eval_mul,eval_lit,hi]
  norm_num

 theorem c4_semantics (v : ℚ) (env : ℕ→ℝ) (hu : 0<h+(v:ℝ)) :
    Expr.eval env (c4Expr v)=c4Floor v := by
  have hm : 0<Expr.eval env (add (dv (lit 6) (sq (.namedConst .pi)))
      (dv (lit (131/125)) (add hExpr (lit v)))) := by
    simp only [eval_add,eval_div,eval_sq,eval_pi,eval_lit,h_semantics]
    norm_num only [Rat.cast_div,Rat.cast_ofNat]
    positivity
  unfold c4Expr
  rw [eval_mul,eval_lit,eval_sq,eval_add,rt_semantics _ _ hm,
    eval_div,eval_mul,eval_lit,rt_semantics _ _ (by simpa using hu)]
  simp only [eval_add,eval_div,eval_sq,eval_pi,eval_lit,h_semantics]
  norm_num only [c4Floor,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat]

 theorem ratio_semantics (v : ℚ) (env : ℕ→ℝ) :
    Expr.eval env (ratioExpr v)=ratioFloor v := by
  simp only [ratioExpr,eval_div,eval_add,eval_mul,eval_sq,eval_pi,eval_lit,
    h_semantics,mzero_semantics]
  norm_num only [ratioFloor,Rat.cast_div,Rat.cast_ofNat]

/-- Denotation of each actually executed Gaussian lower cell. -/
 theorem floorBody_semantics (v start : ℚ) (k : ℕ) (hu : 0<h+(v:ℝ)) :
    Expr.eval (sumBodyRealEnv k) (floorBody v start) =
      (8*(2371/20000:ℝ))*c4Floor v*(3/4096)*
        WinnerOldAnalytic.kernelCell (2371/20000)
          (if start=0 then h+v else h) (ratioFloor v)
          ((start:ℝ)+(3/4096)*(k:ℝ)) ((start:ℝ)+(3/4096)*(k:ℝ)+3/4096) := by
  simp only [floorBody,eval_mul,eval_div,eval_sub,eval_exp,eval_lit,eval_add,eval_sq,
    c4_semantics v _ hu,ratio_semantics]
  split_ifs
  all_goals
    simp only [eval_add,h_semantics,eval_lit,Expr.eval,sumBodyRealEnv]
    norm_num only [WinnerOldAnalytic.kernelCell,Rat.cast_mul,Rat.cast_div,
      Rat.cast_ofNat,Rat.cast_pow,Rat.cast_add]
    simp only [div_eq_mul_inv]
    ring

#print axioms floorBody_semantics
end WinnerOldFloors
