/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40Cell

open scoped BigOperators Interval
open MeasureTheory Set Polynomial
set_option autoImplicit false
namespace RH080.Gaussian40

noncomputable def deltaPoly (a h : ℚ) : Polynomial ℚ :=
  C (2*a*h)*X + C (h*h)*X^2

noncomputable def expNegPoly (a h : ℚ) (n : ℕ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range n, C (((-1 : ℚ)^i) / i.factorial) * deltaPoly a h ^ i

theorem realEval_deltaPoly (a h : ℚ) (t : ℝ) :
    realEval (deltaPoly a h) t = 2*(a : ℝ)*h*t + (h : ℝ)^2*t^2 := by
  simp only [realEval, deltaPoly, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
  change ((2*a*h : ℚ) : ℝ)*t + ((h*h : ℚ) : ℝ)*t^2 = _
  push_cast
  ring

theorem realEval_expNegPoly (a h : ℚ) (n : ℕ) (t : ℝ) :
    realEval (expNegPoly a h n) t =
      ∑ i ∈ Finset.range n, (-(2*(a : ℝ)*h*t + (h : ℝ)^2*t^2))^i /
        (i.factorial : ℝ) := by
  simp only [realEval, expNegPoly, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow]
  apply Finset.sum_congr rfl
  intro i hi
  change ((((-1 : ℚ)^i) / i.factorial : ℚ) : ℝ) * realEval (deltaPoly a h) t ^ i = _
  rw [realEval_deltaPoly]
  push_cast
  simp only [div_mul_eq_mul_div, ← mul_pow, neg_one_mul]

/-- Genuine quadrature error for the polynomial used by the cell generator. -/
theorem expNegPoly_error (a h : ℚ) (ha : 0 ≤ a) (hh : 0 ≤ h) (n : ℕ)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    |Real.exp (-(2*(a : ℝ)*h*t + (h : ℝ)^2*t^2)) -
      realEval (expNegPoly a h n) t| ≤
      ((2*a*h + h*h)^n / (n.factorial : ℚ) : ℚ) := by
  have ha' : 0 ≤ (a : ℝ) := by exact_mod_cast ha
  have hh' : 0 ≤ (h : ℝ) := by exact_mod_cast hh
  have ht0 := ht.1
  have hd : 0 ≤ 2*(a : ℝ)*h*t + (h : ℝ)^2*t^2 := by positivity
  have ht2 : t^2 ≤ (1 : ℝ) := pow_le_one₀ ht.1 ht.2
  have hD : 2*(a : ℝ)*h*t + (h : ℝ)^2*t^2 ≤ 2*(a : ℝ)*h + (h : ℝ)^2 := by
    have h1 := mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ 2*(a : ℝ)*h)
    have h2 := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (h : ℝ))
    nlinarith
  rw [realEval_expNegPoly]
  have htay := exp_neg_taylor_bound _ hd n
  have hpow := pow_le_pow_left₀ hd hD n
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have := htay.trans (div_le_div_of_nonneg_right hpow hfac.le)
  push_cast
  simpa only [pow_two] using this

/-- Analytic soundness of a polynomial-times-Gaussian cell enclosure.
The hypotheses are exact polynomial/range/Taylor data, not numerical samples. -/
theorem gaussian_cell_integral_upper (p q : Polynomial ℚ) (a h M R E : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hbudget : ∀ t ∈ Icc (0 : ℝ) 1, |realEval p t| ≤ M)
    (hrem : ∀ t ∈ Icc (0 : ℝ) 1,
      |Real.exp (-(2*a*h*t+h^2*t^2))-realEval q t| ≤ R)
    (hE : Real.exp (-(a^2)) ≤ E) :
    (∫ t in (0 : ℝ)..1, realEval p t * Real.exp (-((a+h*t)^2))) ≤
      E * (max 0 (unitIntegral (p*q) : ℝ) + M*R) := by
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      realEval p t * Real.exp (-((a+h*t)^2)) ≤
        Real.exp (-(a^2)) * (realEval (p*q) t + M*R) := by
    have hprod : |realEval p t *
        (Real.exp (-(2*a*h*t+h^2*t^2))-realEval q t)| ≤ M*R := by
      rw [abs_mul]
      exact mul_le_mul (hbudget t ht) (hrem t ht) (abs_nonneg _) hM
    have hle := (le_abs_self (realEval p t *
      (Real.exp (-(2*a*h*t+h^2*t^2))-realEval q t))).trans hprod
    have hs : realEval p t * Real.exp (-(2*a*h*t+h^2*t^2)) ≤
        realEval (p*q) t + M*R := by
      simp only [realEval, Polynomial.eval₂_mul] at *
      nlinarith
    have hex : -((a+h*t)^2) = -(a^2) + -(2*a*h*t+h^2*t^2) := by ring
    rw [hex, Real.exp_add]
    nlinarith [mul_le_mul_of_nonneg_left hs (Real.exp_nonneg (-(a^2)))]
  have hc : Continuous (fun t : ℝ => realEval p t * Real.exp (-((a+h*t)^2))) := by
    apply (continuous_realEval p).mul
    exact Real.continuous_exp.comp (((continuous_const.add
      (continuous_const.mul continuous_id)).pow 2).neg)
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hc.intervalIntegrable 0 1)
    (((continuous_realEval (p*q)).add continuous_const).const_mul
      (Real.exp (-(a^2))) |>.intervalIntegrable 0 1) hpoint
  have hright : (∫ t in (0 : ℝ)..1,
      Real.exp (-(a^2)) * (realEval (p*q) t + M*R)) =
      Real.exp (-(a^2))*((unitIntegral (p*q) : ℝ)+M*R) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((continuous_realEval (p*q)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), integral_realEval_unit]
    simp
  change (∫ t in (0 : ℝ)..1, realEval p t * Real.exp (-((a+h*t)^2))) ≤
    (∫ t in (0 : ℝ)..1, Real.exp (-(a^2))*(realEval (p*q) t+M*R)) at hi
  rw [hright] at hi
  have hnonneg : 0 ≤ max 0 (unitIntegral (p*q) : ℝ) + M*R := by positivity
  calc
    _ ≤ Real.exp (-(a^2))*((unitIntegral (p*q) : ℝ)+M*R) := hi
    _ ≤ Real.exp (-(a^2))*(max 0 (unitIntegral (p*q) : ℝ)+M*R) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      linarith [le_max_right (0 : ℝ) (unitIntegral (p*q) : ℝ)]
    _ ≤ E*(max 0 (unitIntegral (p*q) : ℝ)+M*R) :=
      mul_le_mul_of_nonneg_right hE hnonneg

#print axioms expNegPoly_error
#print axioms gaussian_cell_integral_upper
end RH080.Gaussian40
