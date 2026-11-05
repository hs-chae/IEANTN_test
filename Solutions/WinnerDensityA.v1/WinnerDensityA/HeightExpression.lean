/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.ModelProgram
import WinnerDensityA.PiecewiseMoment
namespace WinnerDensityA.HeightExpression
open Real LeanCert.Core LeanCert.Engine WinnerDensityA.Program
set_option maxHeartbeats 0

def lowerExpr (s : Expr) (v : ℚ) : Expr :=
  let r:=dv (sub (mul (lit 8) s) (lit 5)) (lit 3)
  let q:=sub (lit 5) (mul (lit 2) s)
  let h:=add (.log (lit 3000000000000)) (lit v)
  let rh:=mul r h
  mul (dv (.exp (add (.neg (mul r h)) (mul q (.log h)))) r)
    (add (add (add (lit 1) (dv q rh)) (dv (mul q (sub q (lit 1))) (pw rh 2)))
      (dv (mul (mul q (sub q (lit 1))) (sub q (lit 2))) (pw rh 3)))

noncomputable def lowerExp (s h : ℝ) :=
  let r:=(8*s-5)/3
  let q:=5-2*s
  exp (-r*h+q*log h)/r*(1+q/(r*h)+q*(q-1)/(r*h)^2+q*(q-1)*(q-2)/(r*h)^3)

theorem lower_semantics (s : Expr) (v : ℚ) (env : ℕ→ℝ) :
    Expr.eval env (lowerExpr s v)=lowerExp (Expr.eval env s) (log H+(v:ℝ)) := by
  simp only [lowerExpr,Expr.eval,lit,add,mul,sub,dv,pw,
    WinnerProgramA.sub,WinnerProgramA.divE,WinnerProgramA.powE]
  push_cast
  unfold lowerExp
  norm_num only [H]
  ring

theorem lower_real (s v : ℝ) (hv : 0≤v) :
    lowerExp s (log H+v)=Piecewise.lower (8*(1-s)/3) (5-2*s) (H*exp v) := by
  have hH : 0<H := by norm_num [H]
  have hH1 : 1<H := by norm_num [H]
  have hlH : 0<log H := log_pos hH1
  have hA : 0<H*exp v := by positivity
  have hlog : log (H*exp v)=log H+v := by rw [log_mul hH.ne' (exp_ne_zero _),log_exp]
  have hl : 0<log H+v := by linarith
  have hr : 1-8*(1-s)/3=(8*s-5)/3 := by ring
  have hm : (H*exp v)^(8*(1-s)/3-1)*log (H*exp v)^(5-2*s)=
      exp (-((8*s-5)/3)*(log H+v)+(5-2*s)*log (log H+v)) := by
    rw [rpow_def_of_pos hA,hlog,rpow_def_of_pos hl,←exp_add]
    congr 1
    ring
  unfold lowerExp Piecewise.lower
  dsimp only
  rw [hr,hm,hlog]

 theorem initial_upper (s : ℝ) :
    Piecewise.upper (8*(1-s)/3) (5-2*s) H=CH2QRH.densityMomentMain s H := by
  unfold Piecewise.upper CH2QRH.densityMomentMain
  dsimp only

#print axioms lower_semantics
#print axioms lower_real
end WinnerDensityA.HeightExpression
