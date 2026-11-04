/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerProgramA.Program
namespace WinnerProgramA
open LeanCert.Core

/-- Written Taylor-four moment, separate from the executable expression syntax. -/
noncomputable def momentReal (s c d : ℝ) : ℝ :=
  let h := Real.log 3000000000000
  let a := (8*s-5)/3
  let q := 5-2*s
  c*Real.exp (-a*h+q*Real.log h)/a *
    (1+q/(a*h)+q*(q-1)/(a*h)^2+q*(q-1)*(q-2)/(a*h)^3+
      q*(q-1)*(q-2)*(q-3)/(a*h)^4) +
    d/3000000000000*(h^2+2*h+2)

/-- The actual operand-generating syntax evaluates to the stated mathematical expression. -/
theorem moment_semantics (s : Expr) (c d : ℚ) (env : ℕ → ℝ) :
    Expr.eval env (moment s c d) = momentReal (Expr.eval env s) c d := by
  simp only [moment, momentReal, Expr.eval, powE, lit, add, mul, sub, divE]
  push_cast
  ring

#print axioms moment_semantics
end WinnerProgramA
