/- Actual Gaussian functional -> ordinary-RH asymptotic ANT consumers.
The Fourier identity and all numerical facts are proved; the generic CMS
analytic optimization reduction remains the exact explicit source input. -/
import CMSPopulationFunctionalSource
import GaussianEligibility

noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory Filter
namespace RHOnePrime.GaussianGap
open RHOnePrime.GaussianKernel RHOnePrime.GaussianFourier RHOnePrime.CMSFunctional IEANTN.CMSFunctional

/-- For each epsilon>0, every sufficiently large zero-based prime index n has
normalized consecutive-prime gap at most .834021+epsilon. No explicit onset. -/
theorem gaussian_gap_eventually (hCMS : SourceCMSFunctional) (rh : RiemannHypothesis) :
    EventualGapBound (834021/1000000 : ℝ) :=
  bound_mono (gap_from_functional hCMS gaussian_eligible gaussian_denominator_pos rh)
    gaussian_inverse_upper

/-- Strict eventual comparison against the fixed displayed2026 coefficient.
This is not an exhaustive best-known-result or an optimality claim. -/
theorem gaussian_gap_eventually_lt_printed_2026
    (hCMS : SourceCMSFunctional) (rh : RiemannHypothesis) :
    ∀ᶠ n : ℕ in atTop, normalizedGap n < (834050619151/1000000000000 : ℝ) := by
  have h := gaussian_gap_eventually hCMS rh (29619151/2000000000000) (by norm_num)
  filter_upwards [h] with n hn
  linarith

/-- The same proved Fourier/norm/leakage witness gives a whole asymptotic
population curve via exact CMS Theorem3. Strict width slack is explicit. -/
theorem gaussian_population_curve (hCMS : SourceCMSPopulation) (rh : RiemannHypothesis)
    {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) :
    GoodCoefficient α ((834021/1000000 : ℝ)*(1+2*α)+ε) := by
  apply population_from_functional hCMS gaussian_eligible gaussian_denominator_pos rh hα
  have hsum : 0 ≤ 1+2*α := by linarith
  have hm := mul_le_mul_of_nonneg_left gaussian_inverse_upper hsum
  nlinarith

theorem gaussian_population_eventually (hCMS : SourceCMSPopulation) (rh : RiemannHypothesis)
    {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, α*sqrt x <
      (halfOpenCount ((834021/1000000 : ℝ)*(1+2*α)+ε) x : ℝ) :=
  eventual_count_of_good (gaussian_population_curve hCMS rh hα hε)

/-- Pointwise comparison of displayed asymptotic upper-bound curves only.
It does not compare this curve with every stronger2026 population bound. -/
theorem gaussian_curve_lt_old_CPJ {α : ℝ} (hα : 0 ≤ α) :
    (834021/1000000 : ℝ)*(1+2*α) < (4179/5000 : ℝ)*(1+2*α) := by
  nlinarith

#print axioms gaussian_eligible
#print axioms gaussian_denominator_pos
#print axioms gaussian_inverse_upper
#print axioms gaussian_gap_eventually
#print axioms gaussian_gap_eventually_lt_printed_2026
#print axioms gaussian_population_curve
#print axioms gaussian_population_eventually
end RHOnePrime.GaussianGap
