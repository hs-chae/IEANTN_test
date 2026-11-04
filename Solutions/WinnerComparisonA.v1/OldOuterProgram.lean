/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerProgramA.Program
namespace WinnerOldOuter
open LeanCert.Core LeanCert.Engine Real
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev lit := Expr.const
abbrev add := Expr.add
abbrev mul := Expr.mul
def sub (a b : Expr) := add a (.neg b)
def dv (a b : Expr) := mul a (.inv b)
def sq (a : Expr) := mul a a
def mass (k : Expr) : Expr := dv (sub (lit 1) (Expr.exp (.neg (mul k (lit (1/40)))))) k

def outerBody (v0 step U V : ℚ) : Expr :=
  let vl := add (lit v0) (mul (lit step) (.var 0))
  let vr := add vl (lit step)
  let ul := add (Expr.log (lit 3000000000000)) vl
  let ur := add (Expr.log (lit 3000000000000)) vr
  let dl := add (add (Expr.log (lit (U/V))) (Expr.log ul)) (mul (lit (4/3)) ul)
  let dr := add (add (Expr.log (lit (U/V))) (Expr.log ur)) (mul (lit (4/3)) ur)
  let p := lit (2*(3663/10000)+2*(3599/10000)*(2*(7/8)-1))
  let al := add (lit (1/4)) (dv p (add ur (lit (3599/5000))))
  let au := add (lit (1/4)) (dv p (add ul (lit (3599/5000))))
  let zl := mul (lit (499999/1000000)) (Expr.exp (add (lit (2371/10000))
    (sub (add (add (mul al dl) (Expr.log (lit V))) (mul (lit 2) (Expr.log ul))) ur)))
  let zu := mul (lit (501/1000)) (Expr.exp (add (lit (2371/10000))
    (sub (add (add (mul au dr) (Expr.log (lit V))) (mul (lit 2) (Expr.log ur))) ul)))
  let bl := mul (sub (lit 2) (dv (lit (3599/2500)) (add ur (lit (3599/5000))))) dl
  let bu := mul (sub (lit 2) (dv (lit (3599/2500)) (add ul (lit (3599/5000))))) dr
  let rmin := sub (lit 1) (Expr.exp (.neg vl))
  mul (dv (lit (600*step)) (mul (lit (3663/5000)) (.namedConst .pi)))
    (sub (mul ul (mul zl (mass (sub (lit (601/2)) bl))))
      (mul ur (mul (dv (sq zu) (mul (lit 2) rmin)) (mass (sub (lit (601/2)) (mul (lit 2) bu))))))

def cfg : DyadicConfig := { precision := -80, taylorDepth := 20 }
def checkLower (body : Expr) (n : ℕ) (target : ℚ) : Bool :=
  CH2QRH.DensityComputation.checkUpperBound (.neg body) 0 (n-1) (-target) cfg

theorem checkLower_sound (body : Expr) (n : ℕ) (target : ℚ)
    (hc : checkLower body n target=true) :
    (target:ℝ) ≤ ∑ k ∈ Finset.Icc 0 (n-1), Expr.eval (sumBodyRealEnv k) body := by
  have h := CH2QRH.DensityComputation.verify_upper (.neg body) 0 (n-1) (-target) cfg
    (by decide) hc
  simp only [Expr.eval, Finset.sum_neg_distrib, Rat.cast_neg] at h
  linarith


end WinnerOldOuter
