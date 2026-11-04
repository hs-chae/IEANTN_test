/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongMemoProgram
namespace WinnerStrongOuter
open LeanCert.Core LeanCert.Engine WinnerMemoSum
set_option maxHeartbeats 0
set_option maxRecDepth 100000
 def warmRhi (vl vr : Expr) : Expr := add (sub (lit 1) (.exp (.neg vr))) (.exp (.neg (add h vl)))
 def warmFmax (vl vr : Expr) (qright : ℚ) : Expr :=
  let b:=bounds vl vr
  let zmax:=mul b.zl (.exp (mul b.bl (lit qright)))
  dv (mul (mul b.ul b.rmin) (mul (lit 2) zmax))
    (mul (mul (lit (3663/5000)) (.namedConst .pi)) (add (mul (lit 2) (warmRhi vl vr)) zmax))
 def softMin (a b : Expr) : Expr :=
  dv (sub (add a b) (rt (add (sq (sub a b)) (lit (1/1000000000000000000000000))))) (lit 2)
 def bandMass (k : Expr) (a b : ℚ) : Expr :=
  dv (sub (.exp (.neg (mul k (lit a)))) (.exp (.neg (mul k (lit b))))) k
 def warmTerm (v0 step : ℚ) (j : ℕ) : Expr :=
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let b:=bounds vl vr
  let a:ℚ:=(j:ℚ)/500
  let q:ℚ:=((j:ℚ)+1)/500
  mul (softMin (warmFmax vl vr q) b.window)
    (mul (.exp (.neg (mul b.bl (lit q)))) (bandMass (sub (lit (30001/100)) b.bl) a q))
 def warmBody (v0 step : ℚ) : Expr :=
  mul (lit (600*step)) ((List.range 25).foldl (fun acc j=>add acc (warmTerm v0 step j)) (lit 0))
 def warmKeys (v0 step : ℚ) : List Expr :=
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  strongKeys v0 step ++ (warmRhi vl vr :: (List.range 25).map (fun j=>warmFmax vl vr (((j:ℚ)+1)/500)))
 def checkWarm (v0 step target : ℚ) (n : ℕ) : Bool :=
  memoCheck (.neg (warmBody v0 step)) (warmKeys v0 step) 0 (n-1) (-target) cfg
 theorem checkWarm_eq (v0 step target : ℚ) (n : ℕ) :
    checkWarm v0 step target n=CH2QRH.DensityComputation.checkUpperBound
      (.neg (warmBody v0 step)) 0 (n-1) (-target) cfg :=
  memoCheck_eq _ _ _ _ _ _
#print axioms checkWarm_eq
end WinnerStrongOuter
