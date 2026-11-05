/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerBetaA.Paired
import WinnerProgramA.Program
import Lean

namespace WinnerBetaA.Numerical
open LeanCert.Core LeanCert.Engine
open WinnerProgramA

/-- Executed syntax for the paired coefficient; inputs are rational scenario witnesses. -/
def coefficientExpr (β L₀ : ℚ) : Expr :=
  let a := sub (lit 1) (lit β)
  let π : Expr := .namedConst .pi
  add (mul (lit (500001/1000000))
      (add (divE (powE a 2) (mul (lit 2) π))
        (divE (mul (add (lit 2) (.inv π)) a) (lit L₀))))
    (divE (lit (16/5)) (powE (lit L₀) 2))

def baselineExpr (β : ℚ) : Expr := mul (lit 2) (powE (sub (lit 1) (lit β)) 2)
def program (β L₀ : ℚ) : List Row := [⟨coefficientExpr β L₀, 1⟩]
def baseline (β : ℚ) : List Row := [⟨baselineExpr β, 1⟩]

theorem coefficient_semantics (β L₀ : ℚ) (env : ℕ → ℝ) :
    Expr.eval env (coefficientExpr β L₀) = pairedCoefficient β L₀ := by
  simp only [coefficientExpr, pairedCoefficient, Expr.eval, MathConst.toReal,
    add, mul, sub, lit, powE, divE]
  push_cast
  ring

theorem value_semantics (β L₀ : ℚ) : value (program β L₀) = pairedCoefficient β L₀ := by
  simp [value, program, rowValue, coefficient_semantics]

def check (β L₀ target : ℚ) : Bool := acceptUpper (run (program β L₀)) [target]
def baselineCheck : Bool := acceptUpper (run (baseline (9/10))) [20000000001/1000000000000]

def allChecks : Bool := baselineCheck && check (9/10) 160 (16453/10000000) &&
  check (9/10) 200 (14554/10000000) && check (9/10) 240 (13344/10000000) &&
    check (7/8) 200 (2048/1000000) && check (7/8) 240 (19027/10000000)

/-- One finite native fact evaluates all six actual interval applications and domain checks. -/
theorem all_checks : allChecks = true := by native_decide

/-- A source-linked certified coefficient is consumed by the analytic paired envelope. -/
theorem coefficient_upper (β L₀ target : ℚ) (h : check β L₀ target = true) :
    pairedCoefficient β L₀ ≤ (target : ℝ) := by
  have hs := source_linked_upper (program β L₀) (run (program β L₀)) [target] rfl h
  simpa only [value_semantics, List.sum_cons, List.sum_nil, add_zero] using hs

theorem coefficient_160 : pairedCoefficient (9/10) 160 ≤ (16453/10000000 : ℝ) := by
  have h := all_checks
  simp only [allChecks, Bool.and_eq_true] at h
  convert coefficient_upper (9/10) 160 (16453/10000000) (by tauto) using 1 <;> norm_num

theorem coefficient_200 : pairedCoefficient (9/10) 200 ≤ (14554/10000000 : ℝ) := by
  have h := all_checks
  simp only [allChecks, Bool.and_eq_true] at h
  convert coefficient_upper (9/10) 200 (14554/10000000) (by tauto) using 1 <;> norm_num

theorem coefficient_240 : pairedCoefficient (9/10) 240 ≤ (13344/10000000 : ℝ) := by
  have h := all_checks
  simp only [allChecks, Bool.and_eq_true] at h
  convert coefficient_upper (9/10) 240 (13344/10000000) (by tauto) using 1 <;> norm_num

theorem coefficient_seven_eighths : pairedCoefficient (7/8) 200 ≤ (2048/1000000 : ℝ) := by
  have h := all_checks
  simp only [allChecks, Bool.and_eq_true] at h
  convert coefficient_upper (7/8) 200 (2048/1000000) (by tauto) using 1 <;> norm_num

theorem coefficient_seven_eighths_240 : pairedCoefficient (7/8) 240 ≤ (19027/10000000 : ℝ) := by
  have h := all_checks
  simp only [allChecks, Bool.and_eq_true] at h
  convert coefficient_upper (7/8) 240 (19027/10000000) (by tauto) using 1 <;> norm_num

#print axioms coefficient_200
#print axioms coefficient_seven_eighths
end WinnerBetaA.Numerical
