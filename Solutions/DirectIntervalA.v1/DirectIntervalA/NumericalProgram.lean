/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerProgramA.Program

/-! Two genuinely composed exact-dyadic programs. Program A evaluates the
moment expression at each left endpoint. Program B uses the actual upper
endpoint returned by A as a rational literal; it has no independent cap table. -/

namespace DirectIntervalA.Numerical
open LeanCert.Core LeanCert.Engine WinnerProgramA
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def cells : ℕ := 512
def kq : ℚ := 201 / 100
def stepq : ℚ := 1 / 4096
def sigmaq (i : Fin cells) : ℚ := 3 / 4 + (i.val : ℚ) / 4096

def uExpr : Expr := add (lit 66) (.log (lit kq))

def momentExpr (s : Expr) : Expr :=
  let b := divE (sub (mul (lit 8) s) (lit 5)) (lit 3)
  let p := sub (lit 5) (mul (lit 2) s)
  let z := mul b uExpr
  let f1 := p
  let f2 := mul f1 (sub p (lit 1))
  let f3 := mul f2 (sub p (lit 2))
  let f4 := mul f3 (sub p (lit 3))
  let poly := add (add (add (add (lit 1) (divE f1 z))
    (divE f2 (powE z 2))) (divE f3 (powE z 3))) (divE f4 (powE z 4))
  add (mul (lit (1959/200))
      (divE (mul (.exp (add (.neg (mul b uExpr)) (mul p (.log uExpr)))) poly) b))
    (mul (lit (893/200))
      (mul (.exp (.neg uExpr)) (add (add (powE uExpr 2) (mul (lit 2) uExpr)) (lit 2))))

def momentRow (i : Fin cells) : Row := ⟨momentExpr (lit (sigmaq i)), 1⟩
def momentProgram : List Row := List.ofFn momentRow

def momentOutput (i : Fin cells) : IntervalDyadic × Bool := runRow (momentRow i)
/-- This is the actual returned upper endpoint, not an externally proposed bound. -/
def momentCap (i : Fin cells) : ℚ := (momentOutput i).1.hi.toRat

theorem moment_execution (i : Fin cells) :
    Exec [momentRow i] [momentOutput i] := rfl

theorem moments_execution : Exec momentProgram (run momentProgram) := rfl

def weightExpr (i : Fin cells) : Expr :=
  mul (lit (2*kq))
    (mul (.exp (sub (lit 66) (mul (lit 330) (sub (lit 1) (lit (sigmaq i))))))
      (sub (.exp (lit (330*stepq))) (lit 1)))

/-- A's actual dyadic result is an input of B's generated syntax. -/
def weightedExpr (i : Fin cells) : Expr := mul (weightExpr i) (lit (momentCap i))

def sumExpr : List Expr → Expr
  | [] => lit 0
  | e :: es => add e (sumExpr es)

def budgetExpr : Expr := sumExpr (List.ofFn weightedExpr)
def budgetRow : Row := ⟨budgetExpr, 1⟩
def budgetProgram : List Row := [budgetRow]
def budgetOutput : IntervalDyadic × Bool := runRow budgetRow

theorem budget_execution : Exec budgetProgram [budgetOutput] := rfl

def target : ℚ := 179257 / 500000

end DirectIntervalA.Numerical
