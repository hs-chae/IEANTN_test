import FKS2SumBridge.Instances

namespace FKS2SumBridge
open FKS2Scalar SumStability

/-- Index views of the extracted source values, not independently specified term arrays. -/
def term1 (k : ℕ) : ℚ := (terms1[k - 3]?).getD 0
def term2 (k : ℕ) : ℚ := (terms2[k - 3]?).getD 0

def epsilon1 (k : ℕ) : ℚ :=
  max |term1 k - expLo (x1 k)| |term1 k - expHi (x1 k)|

def epsilon2 (k : ℕ) : ℚ :=
  max |term2 k - expLo (x2lo k)| |term2 k - expHi (x2hi k)|

def termError1 : ℚ := ∑ k ∈ Finset.Icc 3 43, epsilon1 k
def termError2 : ℚ := ∑ k ∈ Finset.Icc 3 44, epsilon2 k

def roundError1 : ℚ := gamma 40 * (terms1.map abs).sum
def roundError2 : ℚ := gamma 41 * (terms2.map abs).sum

def sumError1 : ℚ := roundError1 + termError1
def sumError2 : ℚ := roundError2 + termError2

theorem extracted_sum_indexing :
    terms1.sum = ∑ k ∈ Finset.Icc 3 43, term1 k ∧
    terms2.sum = ∑ k ∈ Finset.Icc 3 44, term2 k := by
  native_decide

theorem interval_error (v a lo hi : ℝ) (hl : lo ≤ a) (hh : a ≤ hi) :
    |v - a| ≤ max |v - lo| |v - hi| := by
  have h1 := le_max_left |v - lo| |v - hi|
  have h2 := le_max_right |v - lo| |v - hi|
  have ha := (abs_le.mp (show |v - lo| ≤ max |v - lo| |v - hi| from h1)).2
  have hb := (abs_le.mp (show |v - hi| ≤ max |v - lo| |v - hi| from h2)).1
  rw [abs_le]
  constructor <;> linarith

/-- This envelope includes literal/argument rounding and the actual floating helper error:
its center is the helper output extracted from source; its target uses the exact IEANTN argument. -/
theorem first_term_error (k : ℕ) (hk : k ∈ Finset.Icc 3 43) :
    |(term1 k : ℝ) - Real.exp (30 * ((1 : ℝ) / k - 1 / 3))| ≤ (epsilon1 k : ℝ) := by
  have h := expCheck_sound (sum1_checks k hk)
  have ht : (x1 k : ℝ) = 30 * ((1 : ℝ) / k - 1 / 3) := by simp [x1]
  rw [ht] at h
  have he := interval_error (term1 k : ℝ) _ _ _ h.1 h.2
  simpa [epsilon1, Rat.cast_max, Rat.cast_abs] using he

theorem second_term_error (k : ℕ) (hk : k ∈ Finset.Icc 3 44) :
    |(term2 k : ℝ) - Real.exp ((44 * Real.log 2) * ((1 : ℝ) / k - 1 / 3))| ≤
      (epsilon2 k : ℝ) := by
  have hl := (expCheck_sound (sum2_checks k hk).1).1
  have hh := (expCheck_sound (sum2_checks k hk).2).2
  have harg := x2_bounds k hk
  have he := interval_error (term2 k : ℝ) _ _ _
    (hl.trans (Real.exp_le_exp.mpr harg.1))
    ((Real.exp_le_exp.mpr harg.2).trans hh)
  simpa [epsilon2, Rat.cast_max, Rat.cast_abs] using he

theorem terms_to_IEANTN :
    |exactSum terms1 - FKS2Scalar.sum1| ≤ (termError1 : ℝ) ∧
    |exactSum terms2 - FKS2Scalar.sum2| ≤ (termError2 : ℝ) := by
  constructor
  · change |(terms1.sum : ℝ) - FKS2Scalar.sum1| ≤ (termError1 : ℝ)
    rw [extracted_sum_indexing.1]
    simp only [Rat.cast_sum, FKS2Scalar.sum1, termError1, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k hk => first_term_error k hk))
  · change |(terms2.sum : ℝ) - FKS2Scalar.sum2| ≤ (termError2 : ℝ)
    rw [extracted_sum_indexing.2]
    simp only [Rat.cast_sum, FKS2Scalar.sum2, termError2, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k hk => second_term_error k hk))

/-- Both numerical accumulation terms genuinely consume the preexisting symbolic C theorem. -/
theorem IEANTN_sum_errors :
    |(acc1 : ℝ) - FKS2Scalar.sum1| ≤ (sumError1 : ℝ) ∧
    |(acc2 : ℝ) - FKS2Scalar.sum2| ≤ (sumError2 : ℝ) := by
  have h1 := rounding_bounds.1
  have h2 := rounding_bounds.2
  have ht := terms_to_IEANTN
  constructor
  · calc
      _ ≤ |(acc1 : ℝ) - exactSum terms1| + |exactSum terms1 - FKS2Scalar.sum1| :=
        abs_sub_le _ _ _
      _ ≤ (roundError1 : ℝ) + (termError1 : ℝ) := by
        simpa [roundError1, sumAbs] using add_le_add h1 ht.1
      _ = _ := by simp [sumError1]
  · calc
      _ ≤ |(acc2 : ℝ) - exactSum terms2| + |exactSum terms2 - FKS2Scalar.sum2| :=
        abs_sub_le _ _ _
      _ ≤ (roundError2 : ℝ) + (termError2 : ℝ) := by
        simpa [roundError2, sumAbs] using add_le_add h2 ht.2
      _ = _ := by simp [sumError2]

end FKS2SumBridge
