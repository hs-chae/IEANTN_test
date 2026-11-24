/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! A literal Table 4 row in arXiv:2301.13457v2 cannot satisfy Theorem 3.2
at its stated onset. This does not identify the corrected source theorem.
No result about primes, RH or the journal version is asserted here. -/
namespace RHOnePrimeEvolution.Lee2023Literal
open Real

theorem table4_first_row_negative :
    (186054 / 100000 : ℝ) * sqrt (exp 10) * log (exp 10) - 831357 / 100 < 0 := by
  have hsqrt : sqrt (exp (10 : ℝ)) = exp 5 := by
    rw [show (10 : ℝ) = (2 : ℕ) * 5 by norm_num, Real.exp_nat_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have he : exp (5 : ℝ) < (243 : ℝ) := by
    have h := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
      (by norm_num : (5 : ℕ) ≠ 0)
    norm_num [← Real.exp_nat_mul] at h
    exact h
  rw [hsqrt, Real.log_exp]
  linarith

theorem no_nonnegative_quantity_satisfies_row (a : ℝ) (ha : 0 ≤ a) :
    ¬ a < (186054 / 100000 : ℝ) * sqrt (exp 10) * log (exp 10) - 831357 / 100 := by
  linarith [table4_first_row_negative]

/-- The journal version has a different first-row k3, but the same negative-RHS
problem. The source comparison must keep the two written versions separate. -/
theorem published_table4_first_row_negative :
    (167943 / 100000 : ℝ) * sqrt (exp 10) * log (exp 10) - 831357 / 100 < 0 := by
  have h := table4_first_row_negative
  rw [Real.log_exp] at h ⊢
  nlinarith [Real.sqrt_nonneg (exp (10 : ℝ))]

#print axioms table4_first_row_negative
#print axioms no_nonnegative_quantity_satisfies_row
#print axioms published_table4_first_row_negative
end RHOnePrimeEvolution.Lee2023Literal
