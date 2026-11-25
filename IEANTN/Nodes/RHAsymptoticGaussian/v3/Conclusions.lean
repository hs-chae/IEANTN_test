/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.CMSFunctional

namespace RHAsymptoticGaussian.v3
open Real Filter IEANTN.CMSFunctional
/-- Every positive epsilon gives an eventual consecutive-prime gap bound at
the exact certified Fourier quotient. No explicit numerical onset is asserted. -/
def normalized_gap : Prop := EventualGapBound (82325773717/98718416336 : ℝ)
/-- Strict eventual readable upper bound, with its positive slack retained. -/
def gap_below_readable : Prop := ∀ᶠ n : ℕ in atTop,
  normalizedGap n < (833945448/1000000000 : ℝ)
/-- Strict eventual comparison against the preserved exact v2 coefficient. -/
def gap_below_v2 : Prop := ∀ᶠ n : ℕ in atTop,
  normalizedGap n < (2746403660/3293251743 : ℝ)
/-- Strict eventual comparison against the preserved v1 coefficient. -/
def gap_below_v1 : Prop := ∀ᶠ n : ℕ in atTop,
  normalizedGap n < (834021/1000000 : ℝ)
/-- Strict eventual comparison against the fixed printed2026 coefficient.
No global best-known or optimality claim follows from this comparison. -/
def gap_below_printed_2026 : Prop := ∀ᶠ n : ℕ in atTop,
  normalizedGap n < (834050619151/1000000000000 : ℝ)
/-- Whole asymptotic population-width curve from the same actual witness.
Positive epsilon is essential; no infimum attainment is asserted. -/
def population_curve : Prop := ∀ α : ℝ, 0 ≤ α → ∀ ε : ℝ, 0 < ε →
  GoodCoefficient α ((82325773717/98718416336 : ℝ)*(1+2*α)+ε)
/-- Actual source half-open prime counts, without an explicit onset. -/
def population_count : Prop := ∀ α : ℝ, 0 ≤ α → ∀ ε : ℝ, 0 < ε →
  ∀ᶠ x : ℝ in atTop, α*sqrt x <
    (halfOpenCount ((82325773717/98718416336 : ℝ)*(1+2*α)+ε) x : ℝ)
end RHAsymptoticGaussian.v3
