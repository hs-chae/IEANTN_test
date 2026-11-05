/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import StrongOuterProgram
import MemoDensitySum
namespace WinnerStrongOuter
open LeanCert.Core LeanCert.Engine WinnerMemoSum
set_option maxRecDepth 100000
set_option maxHeartbeats 0
 def strongKeys (v0 step : ℚ) : List Expr :=
  let vl:=add (lit v0) (mul (lit step) (.var 0))
  let vr:=add vl (lit step)
  let ul:=add h vl
  let ur:=add h vr
  let U:=ulower vr
  let V:=vlower vl vr
  let b:=bounds vl vr
  h :: mz :: ul :: ur :: U :: V :: (.log (dv U V)) :: (.log ul) :: (.log ur) :: (.log V) :: b.zl :: b.zu :: b.bl :: b.bu :: b.rmin :: b.window :: []
 def checkMainMemo (v0 step width target : ℚ) (n : ℕ) : Bool :=
  memoCheck (.neg (mainBody v0 step width)) (strongKeys v0 step) 0 (n-1) (-target) cfg
 def checkCapMemo (v0 step width : ℚ) (n : ℕ) : Bool :=
  (List.range n).all (fun k=>memoCheck (capBody v0 step width) (strongKeys v0 step) k k 0 cfg)
 theorem checkMainMemo_eq (v0 step width target : ℚ) (n : ℕ) :
    checkMainMemo v0 step width target n=checkMain v0 step width target n := by
  exact memoCheck_eq _ _ _ _ _ _
 theorem checkCapMemo_eq (v0 step width : ℚ) (n : ℕ) :
    checkCapMemo v0 step width n=checkCap v0 step width n := by
  simp only [checkCapMemo,checkCap,memoCheck_eq]
#print axioms checkMainMemo_eq
#print axioms checkCapMemo_eq
end WinnerStrongOuter
