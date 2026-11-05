/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerProgramA.Program
import Mathlib.Analysis.Real.Pi.Bounds
namespace WinnerOldFloors
open LeanCert.Core LeanCert.Engine Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev lit := Expr.const
abbrev add := Expr.add
abbrev mul := Expr.mul
def sub (a b : Expr) := add a (.neg b)
def dv (a b : Expr) := mul a (.inv b)
def sq (a : Expr) := mul a a
def rt (a : Expr) := Expr.exp (dv (Expr.log a) (lit 2))
def hExpr : Expr := Expr.log (lit 3000000000000)
def mzero : Expr := rt (add (lit 1) (mul (lit (2/3)) (rt (lit (6/5)))))
def c4Expr (v : ℚ) : Expr :=
  let u := add hExpr (lit v)
  mul (lit ((611/1000)^2)) (sq (add
    (rt (add (dv (lit 6) (sq (.namedConst .pi))) (dv (lit (131/125)) u)))
    (dv (lit 1) (mul (lit (1461/1000)) (rt u)))))
def ratioExpr (v : ℚ) : Expr :=
  dv (mul (mul (.namedConst .pi) mzero) (lit (31/50)))
    (add (mul (dv (lit 6) (sq (.namedConst .pi))) (add hExpr (lit v))) (lit (131/125)))
def floorBody (v start : ℚ) : Expr :=
  let step : ℚ := 3/4096
  let l := add (lit start) (mul (lit step) (.var 0))
  let r := add l (lit step)
  let den := if start=0 then add hExpr (lit v) else hExpr
  mul (lit ((8*(2371/20000))*step)) (mul (c4Expr v)
    (mul (Expr.exp (sub (mul (lit 2) l) (mul (lit (2371/10000)) (Expr.exp (mul (lit 2) r)))))
      (mul (Expr.exp (dv l (lit 3)))
        (mul (sq (add (lit 1) (dv l den))) (add (Expr.exp l) (ratioExpr v))))))
def cfg : DyadicConfig := { precision := -80, taylorDepth := 20 }

def checkLower (body : Expr) (target : ℚ) : Bool :=
  CH2QRH.DensityComputation.checkUpperBound (.neg body) 0 4095 (-target) cfg

theorem checkLower_sound (body : Expr) (target : ℚ)
    (hc : checkLower body target=true) :
    (target:ℝ) ≤ ∑ k ∈ Finset.Icc 0 4095, Expr.eval (sumBodyRealEnv k) body := by
  have h := CH2QRH.DensityComputation.verify_upper (.neg body) 0 4095 (-target) cfg
    (by decide) hc
  simp only [Expr.eval, Finset.sum_neg_distrib, Rat.cast_neg] at h
  linarith


end WinnerOldFloors
