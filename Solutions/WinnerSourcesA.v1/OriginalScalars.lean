/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DensityCachedSum
import Mathlib.Tactic
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace WinnerOriginalScalars
open LeanCert.Core LeanCert.Engine
abbrev lit := Expr.const
abbrev add := Expr.add
abbrev mul := Expr.mul
def sub (a b : Expr) := add a (.neg b)
def dv (a b : Expr) := mul a (.inv b)
def sq (a : Expr) := mul a a
def rt (a : Expr) := Expr.exp (dv (Expr.log a) (lit 2))
abbrev pival : Expr := .namedConst .pi
abbrev h0 : Expr := lit 3000000000000
abbrev alpha : Expr := lit (601/5000)
abbrev delta : Expr := lit (3119/10000)
abbrev dd : Expr := lit (851/2500)
abbrev eta : Expr := lit (507/2000)
abbrev mu : Expr := lit (1237/1000)
def h : Expr := .log h0
def mzero : Expr := rt (add (lit 1) (mul (lit (2/3)) (rt (lit (6/5)))))
def mone : Expr := add (dv (lit 6) (sq pival)) (dv (lit (131/125)) h)
def mtwo : Expr := add (add (dv (mul (mul pival mzero) (lit (31/50))) h)
  (dv (mul (lit 6) mzero) (mul pival h0)))
  (dv (mul (mul pival mzero) (lit (131/125))) (mul h0 h))
def rootHeight : Expr := .exp (dv h (lit 6))
def rzero : Expr := dv (lit (1413/500)) (mul (mul (lit (309/500)) rootHeight) h)
def rone : Expr := .inv (mul (mul (mul (lit (309/500)) rootHeight) h) (rt h))
def omega : Expr := .exp (dv alpha (mul (lit 2) (sq h0)))

/-- The source right-moment constants with the harmless upper gamma<=1. -/
def cFive : Expr := mul (dv (mul (mul pival mzero) (lit (529/1000))) (mul (lit 2) delta))
  (mul (sq (add (lit 1) (dv (mul (lit 2) delta) h))) (.exp (dv (mul (lit 2) delta) h)))
def cSix : Expr := add
  (mul (dv (lit (529/1000)) (mul (mul (lit 5) delta) (.exp delta)))
    (sq (add (lit 1) (dv delta h))))
  (dv (mul (lit (121/200)) (.exp (.neg (mul (lit 2) delta)))) (sq h))
def rightV : Expr :=
  let s2 := add (lit 1) (dv delta h)
  let om := .exp (mul (mul (lit 2) alpha) (sq (dv s2 h0)))
  let i1 := .inv (mul (lit 4) alpha)
  let i2 := dv (rt pival) (mul (mul (lit 8) alpha) (rt (mul (lit 2) alpha)))
  mul (mul (mul (lit 8) alpha) om)
    (add (mul (add cFive (dv (mul (mul cSix pival) mzero) h0)) i1) (mul cSix i2))

/-- Conservative source b6 with gamma replaced by1. -/
def bSix (height param : Expr) : Expr :=
  let l := Expr.log height
  mul (dv (mul (add (lit 1) param) l) (mul param (.exp (mul param l))))
    (add (add (add (lit 1) (.inv (mul param l))) (.inv l))
      (dv (mul (lit 7) param) (mul (mul (mul (lit 12) (add (lit 1) param)) height) l)))
def cSeven : Expr :=
  let b6 := bSix (lit 1000000000) eta
  let b9 := add (mul (dv pival (.log (lit 2)))
    (sub (add (.log (lit 227)) (.log (lit 675)))
      (mul (lit 2) (.log (sub (lit 1) (sq b6)))))) pival
  add (dv (add (mul (lit 2) (add (lit 1) (mul (lit 2) eta)))
    (mul (mul (lit 2) pival) (add (lit 1) eta))) (.log (lit 2))) (dv b9 h)
def bEleven (tau : Expr) : Expr :=
  let z := mul (sub tau (lit 1)) h
  add (add (add (lit 1) (dv (lit 3) z)) (dv (lit 6) (sq z)))
    (dv (lit 6) (mul (sq z) z))
def cEight : Expr :=
  let b6 := bSix h0 (sub mu (lit 1))
  let r := sq b6
  let b10 := dv (.neg (.log (sub (lit 1) r))) r
  mul (dv (mul b10 (sq h)) (.exp (mul (sub (mul (lit 2) mu) (lit 2)) h)))
    (add (dv (mul (mul (lit 4) mu) (bEleven (mul (lit 2) mu))) (sub (mul (lit 2) mu) (lit 1)))
      (dv (mul (mul (mul (lit 2) pival) mzero)
        (mul (sub (mul (lit 2) mu) (lit 1)) (bEleven (sub (mul (lit 2) mu) (lit 1)))))
        (sub mu (lit 1))))

def slopeB : Expr :=
  let rr := add (dv (mul (lit 8) delta) (lit 3))
    (dv (mul (mul (lit 4) delta) (.log h)) (add h (mul (lit 2) delta)))
  let tt := dv (mul (lit 2) delta) (add h (mul (lit 2) delta))
  add (add (mul (lit 2) rr)
    (mul (add (lit (-2)) (mul (lit 2) tt)) (.log (lit (67/50)))))
    (mul (lit 2) (.log (lit (17/2))))
def kappa : Expr :=
  let rr := add (dv (mul (lit 8) delta) (lit 3))
    (dv (mul (mul (lit 4) delta) (.log h)) (add h (mul (lit 2) delta)))
  let tt := dv (mul (lit 2) delta) (add h (mul (lit 2) delta))
  let dterm := add (dv (mul (lit 2) (.log h)) h) (lit (8/3))
  let uexp := add (add (lit (1/4)) (dv (mul (lit 2) dd) h)) (mul tt (lit (3/4)))
  let exponent := add (add (add (mul rr (lit (3/4))) (mul dd dterm)) (mul (lit 2) alpha))
    (add (mul uexp (.log (lit (67/50)))) (mul (lit (3/4)) (.log (lit (17/2)))))
  let b12 := dv (lit (1/2)) (sq (sub (lit 1) (.inv (sub h0 (lit 1)))))
  dv (mul b12 (.exp exponent)) (mul (mul (lit 2) pival) dd)


def cfg : DyadicConfig := { precision := -100, taylorDepth := 32 }
noncomputable def value (e : Expr) : ℝ := Expr.eval (sumBodyRealEnv 0) e

theorem closed_upper (e : Expr) (q : ℚ)
    (hc : CH2QRH.DensityComputation.checkUpperBound e 0 0 q cfg = true) : value e ≤ q := by
  have h := CH2QRH.DensityComputation.verify_upper e 0 0 q cfg (by decide) hc
  simpa [value] using h

theorem closed_lower (e : Expr) (q : ℚ)
    (hc : checkFinSumLowerBoundFull e 0 0 q cfg = true) : (q:ℝ) ≤ value e := by
  have h := verify_finsum_lower_full_checked e 0 0 q cfg (by decide) hc
  simpa [value] using h

theorem height_log_lower : (28:ℝ) ≤ value h := by
  have hz := closed_lower h (28) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem mean_one_upper : value mone ≤ 129/200 := by
  have hz := closed_upper mone (129/200) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem mean_two_upper : value mtwo ≤ 23/250 := by
  have hz := closed_upper mtwo (23/250) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem rzero_upper : value rzero ≤ 681/500000 := by
  have hz := closed_upper rzero (681/500000) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem rone_upper : value rone ≤ 23/250000 := by
  have hz := closed_upper rone (23/250000) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem omega_upper : value omega ≤ 1000000000001/1000000000000 := by
  have hz := closed_upper omega (1000000000001/1000000000000) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem rightV_upper : value rightV ≤ 17/2 := by
  have hz := closed_upper rightV (17/2) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem cSeven_upper : value cSeven ≤ 20 := by
  have hz := closed_upper cSeven (20) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem cEight_upper : value cEight ≤ 1 := by
  have hz := closed_upper cEight (1) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem kappa_upper : value kappa ≤ 9 := by
  have hz := closed_upper kappa (9) (by native_decide)
  norm_num at hz ⊢
  exact hz
theorem slope_lower : (113/20:ℝ) ≤ value slopeB := by
  have hz := closed_lower slopeB (113/20) (by native_decide)
  norm_num at hz ⊢
  exact hz
#print axioms mean_one_upper
#print axioms rightV_upper
#print axioms kappa_upper
#print axioms slope_lower
end WinnerOriginalScalars
