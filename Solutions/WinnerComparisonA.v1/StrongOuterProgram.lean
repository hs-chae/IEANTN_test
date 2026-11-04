/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerProgramA.Program
namespace WinnerStrongOuter
open LeanCert.Core LeanCert.Engine
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev lit:=Expr.const
abbrev add:=Expr.add
abbrev mul:=Expr.mul
def sub (a b:Expr):Expr:=add a (.neg b)
def dv (a b:Expr):Expr:=mul a (.inv b)
def sq (a:Expr):Expr:=mul a a
def rt (a:Expr):Expr:=.exp (dv (.log a) (lit 2))
def h:Expr:=.log (lit 3000000000000)
def mz:Expr:=rt (add (lit 1) (mul (lit (2/3)) (rt (lit (6/5)))))
def ulower (v:Expr):Expr:=
  let u:=add h v
  let r:=dv (mul (mul (.namedConst .pi) mz) (lit (31/50)))
    (add (mul (dv (lit 6) (sq (.namedConst .pi))) u) (lit (131/125)))
  let a2:=add (dv (lit (6*(611/1000))) (.exp (lit 1))) (lit (551/20))
  let rz:=dv a2 (mul (mul (lit (611/1000)) (.exp (dv u (lit 6)))) u)
  let c4:=mul (lit ((611/1000)^2)) (sq (add (rt (add (dv (lit 6) (sq (.namedConst .pi))) (dv (lit (131/125)) u)))
    (dv (lit 1) (mul (lit (551/20)) (rt u)))))
  let j0:=lit (24831237/5000000)
  let j1:=lit (40243359/10000000)
  let j2:=lit (42716363/10000000)
  let j3:=lit (4970851/2000000)
  let j4:=lit (13752593/10000000)
  let j5:=lit (15803167/10000000)
  let j6:=lit (21756833/5000000)
  let j7:=lit (4216861/1250000)
  let j8:=lit (5692967/2500000)
  let j9:=lit (2256319/2000000)
  let j10:=lit (38357431/10000000)
  let j11:=lit (10538851/5000000)
  let block (a b c:Expr):Expr:=add (add a (mul (dv (lit 2) u) b)) (dv c (sq u))
  let g:=add (add (block j0 j1 j2) (mul r (block j3 j4 j5)))
    (add (mul (mul (lit 2) rz) (add (add j6 (dv j7 u)) (mul r (add j8 (dv j9 u)))))
      (mul (sq rz) (add j10 (mul r j11))))
  mul (lit (8*(2371/20000))) (mul c4 g)
def vlower (vl vr:Expr):Expr:=
  let ul:=add h vl
  let ur:=add h vr
  let delta:=lit (3599/10000)
  let c5:=mul (mul (dv (mul (mul (.namedConst .pi) mz) (lit (529/1000))) (mul (lit 2) delta))
    (sq (add (lit 1) (dv (mul (lit 2) delta) ur))))
    (.exp (dv (mul (mul (lit 2) delta) (lit (577/1000))) ur))
  let c6:=add (mul (mul (dv (lit (529/1000)) (mul (mul (lit 5) delta) (.exp delta)))
    (sq (add (lit 1) (dv delta ur))))
    (.exp (dv (mul delta (sub (lit (577/1000)) (.log (lit 5)))) ul)))
    (dv (mul (lit (121/200)) (.exp (.neg (mul (lit 2) delta)))) (sq ur))
  add (mul (lit 2) c5) (mul (rt (dv (.namedConst .pi) (lit (2371/10000)))) c6)
structure Bounds where
  ul:Expr
  ur:Expr
  zl:Expr
  zu:Expr
  bl:Expr
  bu:Expr
  rmin:Expr
  window:Expr

def bounds (vl vr:Expr):Bounds:=Id.run do
  let ul:=add h vl
  let ur:=add h vr
  let U:=ulower vr
  let V:=vlower vl vr
  let dl:=add (add (.log (dv U V)) (.log ul)) (mul (lit (4/3)) ul)
  let dr:=add (add (.log (dv U V)) (.log ur)) (mul (lit (4/3)) ur)
  let pp:=lit (2*(3663/10000)+2*(3599/10000)*(3/4))
  let al:=add (lit (1/4)) (dv pp (add ur (lit (3599/5000))))
  let au:=add (lit (1/4)) (dv pp (add ul (lit (3599/5000))))
  let zl:=mul (lit (499999/1000000)) (.exp (add (lit (2371/10000))
    (sub (add (add (mul al dl) (.log V)) (mul (lit 2) (.log ul))) ur)))
  let zu:=mul (lit (501/1000)) (.exp (add (lit (2371/10000))
    (sub (add (add (mul au dr) (.log V)) (mul (lit 2) (.log ur))) ul)))
  let bl:=mul (sub (lit 2) (dv (lit (3599/2500)) (add ur (lit (3599/5000))))) dl
  let bu:=mul (sub (lit 2) (dv (lit (3599/2500)) (add ul (lit (3599/5000))))) dr
  let rmin:=sub (lit 1) (.exp (.neg vl))
  let window:=dv (add (mul (sub (sub h (.log (mul (lit 2) (.namedConst .pi)))) (lit 1)) rmin) vl)
    (mul (lit 4) (.namedConst .pi))
  return ⟨ul,ur,zl,zu,bl,bu,rmin,window⟩
def mass (k:Expr) (width:ℚ):Expr:=dv (sub (lit 1) (.exp (.neg (mul k (lit width))))) k
def mainBody (v0 step width:ℚ):Expr:=
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let b:=bounds vl vr
  mul (dv (lit (600*step)) (mul (lit (3663/5000)) (.namedConst .pi)))
    (sub (mul b.ul (mul b.zl (mass (sub (lit (30001/100)) b.bl) width)))
      (mul b.ur (mul (dv (sq b.zu) (mul (lit 2) b.rmin)) (mass (sub (lit (30001/100)) (mul (lit 2) b.bu)) width))))
def capBody (v0 step width:ℚ):Expr:=
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let b:=bounds vl vr
  sub (dv (mul b.ul (mul b.zl (.exp (mul b.bl (lit width))))) (mul (lit (3663/5000)) (.namedConst .pi))) b.window
def cfg:DyadicConfig:={precision:=-80,taylorDepth:=20}
def checkMain (v0 step width target:ℚ) (n:ℕ):Bool:=
  CH2QRH.DensityComputation.checkUpperBound (.neg (mainBody v0 step width)) 0 (n-1) (-target) cfg
def checkCap (v0 step width:ℚ) (n:ℕ):Bool:=
  (List.range n).all (fun k=>CH2QRH.DensityComputation.checkUpperBound (capBody v0 step width) k k 0 cfg)
end WinnerStrongOuter
