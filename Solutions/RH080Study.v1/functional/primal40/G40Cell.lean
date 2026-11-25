/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import LeanCert.Core.IntervalRat.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-! Actual analytic kernel for an isolated Gaussian numerical-witness experiment.
No numerical witness acceptance or Fourier transform identity is assumed here. -/

open scoped BigOperators Interval
open MeasureTheory Set Polynomial

set_option autoImplicit false
namespace RH080.Gaussian40

noncomputable def realEval (p : Polynomial ℚ) (x : ℝ) : ℝ :=
  p.eval₂ (Rat.castHom ℝ) x

noncomputable def unitIntegral (p : Polynomial ℚ) : ℚ :=
  p.sum fun n c => c / (n + 1)

theorem continuous_realEval (p : Polynomial ℚ) : Continuous (realEval p) :=
  p.continuous_eval₂ (Rat.castHom ℝ)

/-- Exact rational integration of the actual polynomial on the unit interval. -/
theorem integral_realEval_unit (p : Polynomial ℚ) :
    (∫ t in (0 : ℝ)..1, realEval p t) = (unitIntegral p : ℝ) := by
  simp only [realEval, Polynomial.eval₂_eq_sum, unitIntegral, Polynomial.sum]
  rw [intervalIntegral.integral_finsetSum]
  · push_cast
    apply Finset.sum_congr rfl
    intro n hn
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  · intro n hn
    exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _

/-- A negative-axis Taylor remainder. Its derivative bound is exactly one. -/
theorem exp_neg_taylor_bound (d : ℝ) (hd : 0 ≤ d) (n : ℕ) :
    |Real.exp (-d) - ∑ i ∈ Finset.range n, (-d)^i / (i.factorial : ℝ)|
      ≤ d^n / (n.factorial : ℝ) := by
  have hi (i : ℕ) : iteratedDeriv i Real.exp = Real.exp := by
    simpa using iteratedDeriv_exp_const_mul i (1 : ℝ)
  have hb : ∀ x ∈ Set.Icc (-d) 0, ‖iteratedDeriv n Real.exp x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [hi, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hx.2
  have ht := LeanCert.Core.taylor_remainder_bound (f := Real.exp)
    (a := -d) (b := 0) (c := 0) (n := n) (M := 1)
    (by linarith) (by linarith) (by rfl) Real.contDiff_exp hb (by norm_num)
    (-d) (by constructor <;> linarith)
  simpa [hi, Real.norm_eq_abs, abs_neg, abs_of_nonneg hd, div_mul_eq_mul_div,
    mul_comm, div_eq_mul_inv] using ht

/-- Absolute coefficient sum; all bounds are exact rational arithmetic. -/
noncomputable def coefficientBudget (p : Polynomial ℚ) : ℚ :=
  p.sum fun _ c => |c|

/-- A proved unit-cell range enclosure, independent of numerical Gaussian samples. -/
theorem abs_realEval_le_budget (p : Polynomial ℚ) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    |realEval p t| ≤ (coefficientBudget p : ℝ) := by
  rw [realEval, Polynomial.eval₂_eq_sum]
  simp only [coefficientBudget, Polynomial.sum]
  push_cast
  calc
    |∑ n ∈ p.support, (p.coeff n : ℝ) * t^n|
      ≤ ∑ n ∈ p.support, |(p.coeff n : ℝ) * t^n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ p.support, |(p.coeff n : ℝ)| := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 n)]
      have hpow : t^n ≤ (1 : ℝ) := pow_le_one₀ ht.1 ht.2
      simpa only [Rat.cast_abs, mul_one] using mul_le_mul_of_nonneg_left hpow
        (abs_nonneg (p.coeff n : ℝ))

#print axioms integral_realEval_unit
#print axioms exp_neg_taylor_bound
#print axioms abs_realEval_le_budget

end RH080.Gaussian40
