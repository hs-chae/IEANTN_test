/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40Coeffs
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
set_option autoImplicit false
namespace RH080.Gaussian40

/-- A negative exponential enclosure by exact range reduction and a Taylor remainder.
Both numerical hypotheses are rational inequalities, checked in the kernel downstream. -/
theorem exp_neg_upper_reduction (q B U : ℚ) (hq : 0 ≤ q) (m n : ℕ) (hm : 0 < m)
    (hbase : (∑ i ∈ Finset.range n, (-(q / m))^i/(i.factorial : ℚ)) +
      (q/m)^n/(n.factorial : ℚ) ≤ B)
    (hpow : B^m ≤ U) : Real.exp (-(q : ℝ)) ≤ (U : ℝ) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hd : 0 ≤ (q : ℝ)/(m : ℝ) := div_nonneg (by exact_mod_cast hq) hm'.le
  have ht := exp_neg_taylor_bound ((q : ℝ)/m) hd n
  have habs := (le_abs_self (Real.exp (-((q : ℝ)/m)) -
    ∑ i ∈ Finset.range n, (-((q : ℝ)/m))^i/(i.factorial : ℝ))).trans ht
  have hb : Real.exp (-((q : ℝ)/m)) ≤ (B : ℝ) := by
    have hbase' : (∑ i ∈ Finset.range n, (-((q : ℝ)/m))^i/(i.factorial : ℝ)) +
        ((q : ℝ)/m)^n/(n.factorial : ℝ) ≤ (B : ℝ) := by exact_mod_cast hbase
    linarith
  have hpower := pow_le_pow_left₀ (Real.exp_nonneg _) hb m
  have heq : Real.exp (-((q : ℝ)/m))^m = Real.exp (-(q : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [heq] at hpower
  exact hpower.trans (by exact_mod_cast hpow)

/-- Exact affine unit-cell conversion, independent of polynomial arithmetic. -/
theorem integral_affine_cell (f : ℝ → ℝ) (a h : ℝ) :
    h*(∫ t in (0 : ℝ)..1, f (a+h*t)) = ∫ u in a..a+h, f u := by
  have hh := intervalIntegral.smul_integral_comp_add_mul
    (a := (0 : ℝ)) (b := 1) f h a
  simpa only [smul_eq_mul, mul_zero, add_zero, mul_one] using hh

#print axioms exp_neg_upper_reduction
#print axioms integral_affine_cell
end RH080.Gaussian40
