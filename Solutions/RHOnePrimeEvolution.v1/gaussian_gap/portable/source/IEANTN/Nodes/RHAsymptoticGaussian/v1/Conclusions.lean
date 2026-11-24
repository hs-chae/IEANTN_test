import IEANTN.Vocabulary.CMSFunctional

namespace RHAsymptoticGaussian.v1
open Real Filter IEANTN.CMSFunctional
/-- Every epsilon>0 gives an eventual zero-based consecutive-prime gap bound.
No explicit numerical onset is asserted. -/
def normalized_gap : Prop := EventualGapBound (834021/1000000 : ℝ)
/-- Strict eventual comparison with the fixed printed2026 asymptotic constant.
No global best-known/optimality or source-first PV assertion. -/
def gap_below_printed_2026 : Prop := ∀ᶠ n : ℕ in atTop,
  normalizedGap n < (834050619151/1000000000000 : ℝ)
/-- One certified witness gives a full population-width upper curve.
The positive epsilon cannot be removed by claiming infimum attainment. -/
def population_curve : Prop := ∀ α : ℝ, 0 ≤ α → ∀ ε : ℝ, 0 < ε →
  GoodCoefficient α ((834021/1000000 : ℝ)*(1+2*α)+ε)
/-- Actual source half-open prime counts, with no explicit numerical onset. -/
def population_count : Prop := ∀ α : ℝ, 0 ≤ α → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ x : ℝ in atTop, α*sqrt x <
    (halfOpenCount ((834021/1000000 : ℝ)*(1+2*α)+ε) x : ℝ)
end RHAsymptoticGaussian.v1
