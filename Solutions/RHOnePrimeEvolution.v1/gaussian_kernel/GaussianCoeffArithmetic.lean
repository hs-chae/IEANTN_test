import GaussianExpUpper
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RHOnePrime.GaussianKernel

def coeffAdd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a::p, b::q => (a+b)::coeffAdd p q

def coeffScale (a : ℚ) (p : List ℚ) : List ℚ := p.map (a*·)

def coeffMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a::p, q => coeffAdd (coeffScale a q) (0::coeffMul p q)

def coeffPow (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => coeffMul p (coeffPow p n)

def coeffComp : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | a::p, q => coeffAdd [a] (coeffMul q (coeffComp p q))

theorem coeffEval_add (p q : List ℚ) (t : ℝ) :
    coeffEval (coeffAdd p q) t = coeffEval p t + coeffEval q t := by
  induction p generalizing q with
  | nil => simp [coeffAdd, coeffEval]
  | cons a p ih =>
    cases q with
    | nil => simp [coeffAdd, coeffEval]
    | cons b q => simp [coeffAdd, coeffEval, ih]; ring

theorem coeffEval_scale (a : ℚ) (p : List ℚ) (t : ℝ) :
    coeffEval (coeffScale a p) t = (a : ℝ)*coeffEval p t := by
  induction p with
  | nil => simp [coeffScale, coeffEval]
  | cons b p ih => simp [coeffScale, coeffEval] at *; rw [ih]; push_cast; ring

theorem coeffEval_mul (p q : List ℚ) (t : ℝ) :
    coeffEval (coeffMul p q) t = coeffEval p t * coeffEval q t := by
  induction p with
  | nil => simp [coeffMul, coeffEval]
  | cons a p ih =>
    rw [coeffMul, coeffEval_add, coeffEval_scale]
    simp only [coeffEval, Rat.cast_zero, zero_add]
    rw [ih]
    ring

theorem coeffEval_pow (p : List ℚ) (n : ℕ) (t : ℝ) :
    coeffEval (coeffPow p n) t = coeffEval p t ^ n := by
  induction n with
  | zero => simp [coeffPow, coeffEval]
  | succ n ih => rw [coeffPow, coeffEval_mul, ih, pow_succ]; ring

theorem coeffEval_comp (p q : List ℚ) (t : ℝ) :
    coeffEval (coeffComp p q) t = coeffEval p (coeffEval q t) := by
  induction p with
  | nil => simp [coeffComp, coeffEval]
  | cons a p ih =>
    rw [coeffComp, coeffEval_add, coeffEval_mul, ih]
    simp [coeffEval]

/-- Actual computed Taylor coefficients, with no polynomial-support execution. -/
def taylorCoeffs (a h : ℚ) (n : ℕ) : List ℚ :=
  ((List.range n).map fun i =>
    coeffScale (((-1 : ℚ)^i)/(i.factorial : ℚ))
      (coeffPow [0,2*a*h,h*h] i)).foldr coeffAdd []

theorem coeffEval_foldAdd (ps : List (List ℚ)) (t : ℝ) :
    coeffEval (ps.foldr coeffAdd []) t = (ps.map (fun p => coeffEval p t)).sum := by
  induction ps with
  | nil => simp [coeffEval]
  | cons p ps ih => simp [coeffEval_add, ih]

theorem coeffEval_taylorCoeffs (a h : ℚ) (n : ℕ) (t : ℝ) :
    coeffEval (taylorCoeffs a h n) t = realEval (expNegPoly a h n) t := by
  rw [taylorCoeffs, coeffEval_foldAdd, List.map_map, realEval_expNegPoly]
  have hsum (f : ℕ → ℝ) (k : ℕ) :
      ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
    induction k with
    | zero => simp
    | succ k ih => simp [List.range_succ, List.map_append, ih, Finset.sum_range_succ]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Function.comp_apply, coeffEval_scale, coeffEval_pow, coeffEval,
    Rat.cast_zero, mul_zero, add_zero, zero_add]
  push_cast
  simp only [div_mul_eq_mul_div, ← mul_pow, neg_one_mul]
  congr 2
  ring

/-- Product semantics and its exact rational integral, as consumed by every cell. -/
theorem integral_coeff_product (p q : List ℚ) :
    (∫ t in (0 : ℝ)..1, coeffEval p t * coeffEval q t) =
      (coeffMoment 0 (coeffMul p q) : ℝ) := by
  simp_rw [← coeffEval_mul]
  exact integral_coeffEval _

#print axioms coeffEval_comp
#print axioms coeffEval_taylorCoeffs
#print axioms integral_coeff_product
end RHOnePrime.GaussianKernel
