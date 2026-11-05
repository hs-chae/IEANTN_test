/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldOmega
import OriginalSharpScalars
namespace WinnerOldC4Source
open Real Set MeasureTheory LeanCert.Core LeanCert.Engine
open WinnerOldFloors
set_option maxHeartbeats 0
noncomputable def windowMain (v : ℝ) : ℝ :=
  ((h-log (2*Real.pi)-1)*(1-exp (-v))+v)/(4*Real.pi)
noncomputable def coarseCap (v0 v1 U V : ℝ) : ℝ :=
  ((h+v1)/(2*Real.pi*d))*(501/1000)*exp (2*alpha)*
    exp (log V+2*log (h+v1)+interp (17/20) (h+v0)*leftD U V (h+v1)-(h+v0))

namespace WindowProgram
abbrev lit := Expr.const
abbrev add := Expr.add
abbrev mul := Expr.mul
def sub (a b : Expr) := add a (.neg b)
def dv (a b : Expr) := mul a (.inv b)
def hExpr := Expr.log (lit 3000000000000)
def coarseExpr (v0 v1 U V : ℚ) : Expr :=
  let ul:=add hExpr (lit v0)
  let ur:=add hExpr (lit v1)
  let aa:=add (lit (3/10)) (dv (lit (2*(3663/10000)+2*(3599/10000)*(7/10))) (add ul (lit (3599/5000))))
  let DD:=add (add (Expr.log (lit (U/V))) (Expr.log ur)) (mul (lit (4/3)) ur)
  mul (mul (mul (dv ur (mul (lit (3663/5000)) (.namedConst .pi))) (lit (501/1000)))
    (Expr.exp (lit (2371/10000))))
    (Expr.exp (sub (add (add (Expr.log (lit V)) (mul (lit 2) (Expr.log ur))) (mul aa DD)) ul))
def windowExpr (v : ℚ) : Expr :=
  dv (add (mul (sub (sub hExpr (Expr.log (mul (lit 2) (.namedConst .pi)))) (lit 1))
    (sub (lit 1) (Expr.exp (lit (-v))))) (lit v)) (mul (lit 4) (.namedConst .pi))
def diffExpr (v0 v1 U V : ℚ) : Expr := sub (windowExpr v0) (coarseExpr v0 v1 U V)

theorem semantics (v0 v1 U V : ℚ) : WinnerOriginalScalars.value (diffExpr v0 v1 U V)=
    windowMain v0-coarseCap v0 v1 U V := by
  simp only [diffExpr,windowExpr,coarseExpr,WinnerOriginalScalars.value,Expr.eval,
    lit,add,mul,dv,sub,hExpr,LeanCert.Core.MathConst.toReal,
    windowMain,coarseCap,h,interp,leftD,d,delta,alpha]
  push_cast
  ring

theorem scalar0 : coarseCap (13/1000) 1 (1698779/1000000) (36/5)≤windowMain (13/1000) := by
  have hh:=WinnerOriginalScalars.closed_lower
    (diffExpr (13/1000) 1 (1698779/1000000) (36/5)) 0 (by native_decide)
  simp only [semantics] at hh
  norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] at hh
  linarith
theorem scalar1 : coarseCap 1 2 (336493/200000) (719/100)≤windowMain 1 := by
  have hh:=WinnerOriginalScalars.closed_lower (diffExpr 1 2 (336493/200000) (719/100)) 0 (by native_decide)
  simp only [semantics] at hh
  norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] at hh
  linarith
theorem scalar2 : coarseCap 2 4 (1652763/1000000) (179/25)≤windowMain 2 := by
  have hh:=WinnerOriginalScalars.closed_lower (diffExpr 2 4 (1652763/1000000) (179/25)) 0 (by native_decide)
  simp only [semantics] at hh
  norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] at hh
  linarith
theorem scalar3 : coarseCap 4 8 (1602809/1000000) (178/25)≤windowMain 4 := by
  have hh:=WinnerOriginalScalars.closed_lower (diffExpr 4 8 (1602809/1000000) (178/25)) 0 (by native_decide)
  simp only [semantics] at hh
  norm_num only [Rat.cast_zero,Rat.cast_div,Rat.cast_ofNat] at hh
  linarith
end WindowProgram

 theorem windowMain_monotone : Monotone windowMain := by
  intro v w hvw
  have hlog := log_le_sub_one_of_pos (by positivity : 0<2*Real.pi)
  have hpi:=pi_lt_four
  have hcoef : 0≤h-log (2*Real.pi)-1 := by linarith [h_lower]
  have he : exp (-w)≤exp (-v) := exp_le_exp.mpr (by linarith)
  unfold windowMain
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith
#print axioms WindowProgram.scalar0
#print axioms windowMain_monotone
end WinnerOldC4Source
