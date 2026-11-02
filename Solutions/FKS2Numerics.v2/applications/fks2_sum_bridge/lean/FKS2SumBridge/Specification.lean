import FKS2SumBridge.Result

namespace FKS2SumBridge
open FKS2Scalar SumStability

/-- Rational upper bounds for the exact IEANTN exponential sums. -/
def upperSum1 : ℚ := s1hi
def upperSum2 : ℚ := s2hi

/-- The exact sums of all term-generation error envelopes, including argument errors. -/
def specError1 : ℚ := gamma 40 * upperSum1 + (1 + gamma 40) * termError1
def specError2 : ℚ := gamma 41 * upperSum2 + (1 + gamma 41) * termError2

theorem epsilon1_nonneg (k : ℕ) : 0 ≤ epsilon1 k := by
  exact (abs_nonneg _).trans (le_max_left _ _)

theorem epsilon2_nonneg (k : ℕ) : 0 ≤ epsilon2 k := by
  exact (abs_nonneg _).trans (le_max_left _ _)

theorem eta_nonneg : 0 ≤ termError1 ∧ 0 ≤ termError2 := by
  constructor
  · exact Finset.sum_nonneg (fun k _ => epsilon1_nonneg k)
  · exact Finset.sum_nonneg (fun k _ => epsilon2_nonneg k)

theorem absolute_decoded_sums :
    sumAbs terms1 = exactSum terms1 ∧ sumAbs terms2 = exactSum terms2 := by
  constructor
  · simp only [sumAbs, exactSum, sumAbs_eq_sum terms_valid.1]
  · simp only [sumAbs, exactSum, sumAbs_eq_sum terms_valid.2]

theorem sum_abs_term_bounds :
    sumAbs terms1 ≤ FKS2Scalar.sum1 + (termError1 : ℝ) ∧
    sumAbs terms2 ≤ FKS2Scalar.sum2 + (termError2 : ℝ) := by
  rw [absolute_decoded_sums.1, absolute_decoded_sums.2]
  constructor <;> linarith [(abs_le.mp terms_to_IEANTN.1).2,
    (abs_le.mp terms_to_IEANTN.2).2]

/-- Triangle inequality and positivity transport a decoded-term stability bound to exact terms. -/
theorem error_via_exact_sum {out decoded exact eta g : ℝ}
    (hround : |out - decoded| ≤ g * decoded)
    (hterm : |decoded - exact| ≤ eta) (hg : 0 ≤ g) :
    |out - exact| ≤ g * exact + (1 + g) * eta := by
  have hb : decoded ≤ exact + eta := by linarith [(abs_le.mp hterm).2]
  calc
    |out - exact| ≤ |out - decoded| + |decoded - exact| := abs_sub_le _ _ _
    _ ≤ g * decoded + eta := add_le_add hround hterm
    _ ≤ g * (exact + eta) + eta :=
      add_le_add (mul_le_mul_of_nonneg_left hb hg) (le_refl eta)
    _ = g * exact + (1 + g) * eta := by ring

/-- Specification-facing bounds retain every term-generation error. -/
theorem specification_sum_errors :
    |(acc1 : ℝ) - FKS2Scalar.sum1| ≤
      (gamma 40 : ℝ) * FKS2Scalar.sum1 + (1 + (gamma 40 : ℝ)) * (termError1 : ℝ) ∧
    |(acc2 : ℝ) - FKS2Scalar.sum2| ≤
      (gamma 41 : ℝ) * FKS2Scalar.sum2 + (1 + (gamma 41 : ℝ)) * (termError2 : ℝ) := by
  have hg40 : (0 : ℝ) ≤ (gamma 40 : ℝ) := by
    exact_mod_cast (gamma_nonneg (k := 40) (by norm_num))
  have hg41 : (0 : ℝ) ≤ (gamma 41 : ℝ) := by
    exact_mod_cast (gamma_nonneg (k := 41) (by norm_num))
  constructor
  · apply error_via_exact_sum _ terms_to_IEANTN.1 hg40
    simpa only [absolute_decoded_sums.1] using rounding_bounds.1
  · apply error_via_exact_sum _ terms_to_IEANTN.2 hg41
    simpa only [absolute_decoded_sums.2] using rounding_bounds.2

theorem rational_sum_bounds :
    FKS2Scalar.sum1 ≤ (upperSum1 : ℝ) ∧ FKS2Scalar.sum2 ≤ (upperSum2 : ℝ) :=
  ⟨sum1_bounds.2, sum2_bounds.2⟩

/-- Explicit E1/E2 obtained from the specification forms and certified U1/U2. -/
theorem rational_specification_errors :
    |(acc1 : ℝ) - FKS2Scalar.sum1| ≤ (specError1 : ℝ) ∧
    |(acc2 : ℝ) - FKS2Scalar.sum2| ≤ (specError2 : ℝ) := by
  have hg40 : (0 : ℝ) ≤ (gamma 40 : ℝ) := by
    exact_mod_cast (gamma_nonneg (k := 40) (by norm_num))
  have hg41 : (0 : ℝ) ≤ (gamma 41 : ℝ) := by
    exact_mod_cast (gamma_nonneg (k := 41) (by norm_num))
  constructor
  · refine specification_sum_errors.1.trans ?_
    simpa [specError1] using add_le_add_right
      (mul_le_mul_of_nonneg_left rational_sum_bounds.1 hg40)
      ((1 + (gamma 40 : ℝ)) * (termError1 : ℝ))
  · refine specification_sum_errors.2.trans ?_
    simpa [specError2] using add_le_add_right
      (mul_le_mul_of_nonneg_left rational_sum_bounds.2 hg41)
      ((1 + (gamma 41 : ℝ)) * (termError2 : ℝ))

end FKS2SumBridge
