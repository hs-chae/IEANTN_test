/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import HighAnchorIntervalA.ProfileProgram
import HighAnchorIntervalA.Common
import DirectIntervalA.NumericalProgram

/-! Two composed exact-dyadic programs. A evaluates256 factored moments.
B's generated syntax consumes A's actual dyadic upper endpoints, with exact
exponential cell weights and the closed C2 correction. -/
namespace HighAnchorIntervalA.Numerical
open LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def cells : ℕ := 256
def kq : ℚ := 201/92
def stepq : ℚ := 1/2048
def Kq : ℚ := Profile.row.K
def Bq : ℚ := Profile.slope
def lambdaq : ℚ := (11/25)*330+Bq
def sigmaq (i : Fin cells) : ℚ := 3/4+(i.val:ℚ)/2048

def uExpr : Expr := add (lit (693/10)) (.log (lit kq))

def factorExpr (s : Expr) : Expr :=
  let u:=uExpr
  let b:=divE (sub (mul (lit 8) s) (lit 5)) (lit 3)
  let q:=sub (lit 5) (mul (lit 2) s)
  let z:=mul b u
  let f1:=q
  let f2:=mul f1 (sub q (lit 1))
  let f3:=mul f2 (sub q (lit 2))
  let f4:=mul f3 (sub q (lit 3))
  let poly:=add (add (add (add (lit 1) (divE f1 z))
    (divE f2 (powE z 2))) (divE f3 (powE z 3))) (divE f4 (powE z 4))
  divE (mul (.exp (add (mul (sub (lit 1) b) (.log (lit kq)))
    (mul q (.log u)))) poly) b

def momentRow (i : Fin cells) : Row := ⟨factorExpr (lit (sigmaq i)),1⟩
def momentOutput (i : Fin cells) : IntervalDyadic×Bool := runRow (momentRow i)
def momentCap (i : Fin cells) : ℚ := (momentOutput i).1.hi.toRat

theorem moment_execution (i : Fin cells) : Exec [momentRow i] [momentOutput i] := rfl

def weightExpr (i : Fin cells) : Expr :=
  mul (lit (2*Kq*330/lambdaq))
    (mul (.exp (lit (Bq/8)))
      (mul (.exp (mul (lit (-lambdaq)) (sub (lit 1) (lit (sigmaq i)))))
        (sub (.exp (lit (lambdaq*stepq))) (lit 1))))

/-- A's actual returned enclosure endpoint is an operand of B. -/
def weightedExpr (i : Fin cells) : Expr := mul (weightExpr i) (lit (momentCap i))

def correctionExpr : Expr :=
  let u:=uExpr
  mul (lit 12) (mul (add (add (powE u 2) (mul (lit 2) u)) (lit 2))
    (sub (.exp (lit (-330/8))) (.exp (lit (-330/4)))))

def budgetExpr : Expr := add (DirectIntervalA.Numerical.sumExpr (List.ofFn weightedExpr)) correctionExpr
def budgetRow : Row := ⟨budgetExpr,1⟩
def budgetProgram : List Row := [budgetRow]
def budgetOutput : IntervalDyadic×Bool := runRow budgetRow

theorem budget_execution : Exec budgetProgram [budgetOutput] := rfl

def target : ℚ := 918869/1000000
end HighAnchorIntervalA.Numerical
