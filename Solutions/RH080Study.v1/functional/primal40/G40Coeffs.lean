/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import G40Quadrature
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
set_option autoImplicit false
namespace RH080.Gaussian40

/-- Rational polynomial coefficients, ascending degree, with Horner semantics. -/
def coeffEval : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c::cs, t => (c : ℝ) + t*coeffEval cs t

noncomputable def coeffPoly : List ℚ → Polynomial ℚ
  | [] => 0
  | c::cs => C c + X*coeffPoly cs

theorem realEval_coeffPoly (cs : List ℚ) (t : ℝ) :
    realEval (coeffPoly cs) t = coeffEval cs t := by
  induction cs with
  | nil => simp [coeffPoly, coeffEval, realEval]
  | cons c cs ih =>
    simp only [coeffPoly, coeffEval, realEval, Polynomial.eval₂_add,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X] at *
    rw [ih]
    rfl

theorem continuous_coeffEval (cs : List ℚ) : Continuous (coeffEval cs) := by
  have heq : realEval (coeffPoly cs) = coeffEval cs := by
    funext t
    exact realEval_coeffPoly cs t
  rw [← heq]
  exact continuous_realEval (coeffPoly cs)

def coeffMoment : ℕ → List ℚ → ℚ
  | _, [] => 0
  | k, c::cs => c/(k+1) + coeffMoment (k+1) cs

/-- Exact integration of a rational coefficient list, including arbitrary moments. -/
theorem integral_coeffMoment (cs : List ℚ) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t^k * coeffEval cs t) = (coeffMoment k cs : ℝ) := by
  induction cs generalizing k with
  | nil => simp [coeffEval, coeffMoment]
  | cons c cs ih =>
    have heq (t : ℝ) : t^k*coeffEval (c::cs) t =
        (c : ℝ)*t^k + t^(k+1)*coeffEval cs t := by
      simp only [coeffEval, pow_succ]
      ring
    simp_rw [heq]
    have h1 : IntervalIntegrable (fun t : ℝ => (c : ℝ)*t^k) volume 0 1 :=
      (continuous_const.mul (continuous_id.pow k)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => t^(k+1)*coeffEval cs t) volume 0 1 :=
      ((continuous_id.pow (k+1)).mul (continuous_coeffEval cs)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, integral_pow, ih]
    simp [coeffMoment, div_eq_mul_inv]

theorem integral_coeffEval (cs : List ℚ) :
    (∫ t in (0 : ℝ)..1, coeffEval cs t) = (coeffMoment 0 cs : ℝ) := by
  simpa using integral_coeffMoment cs 0

def coeffAbsBudget : List ℚ → ℚ
  | [] => 0
  | c::cs => |c| + coeffAbsBudget cs

theorem coeffAbsBudget_nonneg (cs : List ℚ) : 0 ≤ coeffAbsBudget cs := by
  induction cs with
  | nil => simp [coeffAbsBudget]
  | cons c cs ih => simp only [coeffAbsBudget]; positivity

theorem abs_coeffEval_le (cs : List ℚ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    |coeffEval cs t| ≤ (coeffAbsBudget cs : ℝ) := by
  induction cs with
  | nil => simp [coeffEval, coeffAbsBudget]
  | cons c cs ih =>
    simp only [coeffEval, coeffAbsBudget, Rat.cast_add, Rat.cast_abs]
    calc
      |(c : ℝ)+t*coeffEval cs t| ≤ |(c : ℝ)| + |t*coeffEval cs t| := abs_add_le _ _
      _ ≤ |(c : ℝ)| + (coeffAbsBudget cs : ℝ) := by
        gcongr
        rw [abs_mul, abs_of_nonneg ht.1]
        calc
          t*|coeffEval cs t| ≤ 1*|coeffEval cs t| :=
            mul_le_mul_of_nonneg_right ht.2 (abs_nonneg _)
          _ ≤ (coeffAbsBudget cs : ℝ) := by simpa using ih

/-- Coefficient-wise lower bound accounting for the constant coefficient exactly. -/
def coeffLower : List ℚ → ℚ
  | [] => 0
  | c::cs => c + min 0 (coeffLower cs)

def coeffUpper : List ℚ → ℚ
  | [] => 0
  | c::cs => c + max 0 (coeffUpper cs)

theorem coeffEval_lower (cs : List ℚ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    (coeffLower cs : ℝ) ≤ coeffEval cs t := by
  induction cs with
  | nil => simp [coeffLower, coeffEval]
  | cons c cs ih =>
    simp only [coeffLower, coeffEval, Rat.cast_add, Rat.cast_min, Rat.cast_zero]
    have hmul : min 0 (coeffLower cs : ℝ) ≤ t * coeffEval cs t := by
      by_cases h : 0 ≤ coeffEval cs t
      · exact (min_le_left _ _).trans (mul_nonneg ht.1 h)
      · have he : coeffEval cs t ≤ 0 := le_of_not_ge h
        calc
          min 0 (coeffLower cs : ℝ) ≤ (coeffLower cs : ℝ) := min_le_right _ _
          _ ≤ coeffEval cs t := ih
          _ ≤ t*coeffEval cs t := by nlinarith [ht.2]
    linarith

theorem coeffEval_upper (cs : List ℚ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    coeffEval cs t ≤ (coeffUpper cs : ℝ) := by
  induction cs with
  | nil => simp [coeffUpper, coeffEval]
  | cons c cs ih =>
    simp only [coeffUpper, coeffEval, Rat.cast_add, Rat.cast_max, Rat.cast_zero]
    have hmul : t*coeffEval cs t ≤ max 0 (coeffUpper cs : ℝ) := by
      by_cases h : coeffEval cs t ≤ 0
      · exact (mul_nonpos_of_nonneg_of_nonpos ht.1 h).trans (le_max_left _ _)
      · have he : 0 ≤ coeffEval cs t := le_of_not_ge h
        calc
          t*coeffEval cs t ≤ coeffEval cs t := by nlinarith [ht.2]
          _ ≤ (coeffUpper cs : ℝ) := ih
          _ ≤ max 0 (coeffUpper cs : ℝ) := le_max_right _ _
    linarith

#print axioms integral_coeffEval
#print axioms coeffEval_lower
#print axioms coeffEval_upper
end RH080.Gaussian40
