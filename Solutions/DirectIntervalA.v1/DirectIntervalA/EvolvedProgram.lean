/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import DirectIntervalA.NumericalProgram

/-! Factoring the opposite exponential slopes out of the moment before
quadrature permits 64 cells. The second program still consumes the actual
first-program dyadic upper endpoints. -/
namespace DirectIntervalA.Evolved
open LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def cells : ℕ := 64
def sigmaq (i : Fin cells) : ℚ := 3/4+(i.val:ℚ)/512

def factorExpr (s : Expr) : Expr :=
  let u := Numerical.uExpr
  let b := divE (sub (mul (lit 8) s) (lit 5)) (lit 3)
  let p := sub (lit 5) (mul (lit 2) s)
  let z := mul b u
  let f1 := p
  let f2 := mul f1 (sub p (lit 1))
  let f3 := mul f2 (sub p (lit 2))
  let f4 := mul f3 (sub p (lit 3))
  let poly := add (add (add (add (lit 1) (divE f1 z))
    (divE f2 (powE z 2))) (divE f3 (powE z 3))) (divE f4 (powE z 4))
  divE (mul (.exp (add (mul (sub (lit 1) b) (.log (lit Numerical.kq)))
      (mul p (.log u)))) poly) b

def momentRow (i : Fin cells) : Row := ⟨factorExpr (lit (sigmaq i)),1⟩
def momentOutput (i : Fin cells) : IntervalDyadic×Bool := runRow (momentRow i)
def momentCap (i : Fin cells) : ℚ := (momentOutput i).1.hi.toRat

theorem moment_execution (i : Fin cells) :
    Exec [momentRow i] [momentOutput i] := rfl

def weightExpr (i : Fin cells) : Expr :=
  mul (lit (2*(1959/200)*330/154))
    (mul (.exp (mul (lit (-154)) (sub (lit 1) (lit (sigmaq i)))))
      (sub (.exp (lit (154/512))) (lit 1)))

def weightedExpr (i : Fin cells) : Expr := mul (weightExpr i) (lit (momentCap i))

def correctionExpr : Expr :=
  let u:=Numerical.uExpr
  mul (lit (2*(893/200)))
    (mul (add (add (powE u 2) (mul (lit 2) u)) (lit 2))
      (sub (.exp (lit (-330/8))) (.exp (lit (-330/4)))))

def budgetExpr : Expr := add (Numerical.sumExpr (List.ofFn weightedExpr)) correctionExpr
def budgetRow : Row := ⟨budgetExpr,1⟩
def budgetProgram : List Row := [budgetRow]
def budgetOutput : IntervalDyadic×Bool := runRow budgetRow

theorem budget_execution : Exec budgetProgram [budgetOutput] := rfl

def target : ℚ := 355513/1000000

end DirectIntervalA.Evolved
