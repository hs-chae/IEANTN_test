/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Vocabulary.CMSFunctional

noncomputable section
open Real Filter IEANTN.CMSFunctional
namespace RHWeightedPopulation.v1

def sparseLine (α : ℝ) : ℝ := 944247/1000000+(1163388/1000000)*α
def flatLine (α : ℝ) : ℝ := 9/8+(16/15)*α
def frontier (α : ℝ) : ℝ := min (sparseLine α) (flatLine α)

/-- The first source-verified numerical window supplies a whole eventual
population curve, under RH and the explicitly imported general BR input.
Each alpha has its own eventual threshold; no explicit onset is asserted. -/
def sparse_curve : Prop := ∀ α : ℝ, 0≤α → GoodCoefficient α (sparseLine α)
/-- The zero-leakage program instance supplies the lower large-population slope.
Strict norm slack gives a genuine GoodCoefficient, with no infimum attainment
or erased positive epsilon being assumed. -/
def flat_curve : Prop := ∀ α : ℝ, 0≤α → GoodCoefficient α (flatLine α)
/-- Best of the two actual program instances, not a claim of global optimality. -/
def frontier_curve : Prop := ∀ α : ℝ, 0≤α → GoodCoefficient α (frontier α)
/-- Actual source half-open pi counts, with a positive asymptotic margin and
no explicit numerical onset. -/
def frontier_count : Prop := ∀ α : ℝ, 0≤α →
  ∀ᶠ x : ℝ in atTop, α*sqrt x<(halfOpenCount (frontier α) x : ℝ)
/-- A readable consequence of the first curve, improving the prior2.14891875
coefficient in the eventual metric. Its old onsetexp24 is not transferred. -/
def one_population : Prop := GoodCoefficient 1 (527/250 : ℝ)
/-- Ten-sqrt(x) population at width283/24, compared with the prior octic
asymptotic width12.27391875 in their common coefficient range. -/
def ten_population : Prop := GoodCoefficient 10 (283/24 : ℝ)
/-- Exact scalar comparison with the inversion of PrimeInterval.v4's optimized
leading count. The old theorem also has strict endpoints, onsetexp24 and
coefficient range1.03<=c<=16; those conditions remain in its original node. -/
def below_octic_leading_frontier : Prop := ∀ α : ℝ, 0≤α →
  frontier α<(9/8)*(α+18203/20000)
end RHWeightedPopulation.v1
