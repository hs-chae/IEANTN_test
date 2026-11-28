/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTN.Nodes.RHWeightedPopulation.v1.Conclusions
import IEANTN.Nodes.RHAnalyticFlatPopulation.v1.Conclusions
noncomputable section
open Real Filter IEANTN.CMSFunctional
namespace RHWeightedPopulation.v2

/-- The seven v1 mathematical conclusions are retained exactly. -/
def sparse_curve : Prop := RHWeightedPopulation.v1.sparse_curve
def flat_curve : Prop := RHWeightedPopulation.v1.flat_curve
def frontier_curve : Prop := RHWeightedPopulation.v1.frontier_curve
def frontier_count : Prop := RHWeightedPopulation.v1.frontier_count
def one_population : Prop := RHWeightedPopulation.v1.one_population
def ten_population : Prop := RHWeightedPopulation.v1.ten_population
def below_octic_leading_frontier : Prop := RHWeightedPopulation.v1.below_octic_leading_frontier

def w4Line (α:ℝ):ℝ :=851061745/1000000000+(1505657839/1000000000)*α
def threeFrontier (α:ℝ):ℝ :=min (w4Line α) (RHWeightedPopulation.v1.frontier α)
def fourFrontier (α:ℝ):ℝ :=min (threeFrontier α) (RHAnalyticFlatPopulation.v1.flat64Width α)
def paperFirst (α:ℝ):ℝ :=851127043/1000000000+(1505827/1000000)*α
def paperSecond (α:ℝ):ℝ :=85124642/100000000+(1505237/1000000)*α

/-- Original support-seven population line, derived through its actual
Mellin/MV/zero pipeline and the new full-main C norm node. -/
def w4_curve : Prop :=∀α:ℝ,0≤α→GoodCoefficient α (w4Line α)
/-- Original strict infimum form: a smaller actual good coefficient is
exhibited. This is stronger than membership at the displayed width. -/
def w4_infimum_strict : Prop :=∀α:ℝ,0≤α→sInf (goodCoefficients α)<w4Line α
/-- Minimum of the three completed source-first numerical providers. -/
def three_frontier_curve : Prop :=∀α:ℝ,0≤α→GoodCoefficient α (threeFrontier α)
/-- The actual attained minimum lies below both printed BRv2 lines at every
nonnegative alpha; this is not a global best-known or optimality claim. -/
def actual_below_both_printed_lines : Prop :=∀α:ℝ,0≤α→∃c:ℝ,
  GoodCoefficient α c ∧ c<min (paperFirst α) (paperSecond α)
/-- Hybrid of three source-first numerical providers and the independently
proved kernel-only analytic fixed64 family. This hybrid is not labeled all-PV. -/
def four_frontier_curve : Prop :=∀α:ℝ,0≤α→GoodCoefficient α (fourFrontier α)
/-- Actual half-open prime counts from that hybrid, with strict asymptotic
margin and no transferred finite onset. -/
def four_frontier_count : Prop :=∀α:ℝ,0≤α→∀ᶠx:ℝ in atTop,
  α*sqrt x<(halfOpenCount (fourFrontier α) x:ℝ)

/-- Hybrid downstream use of the adaptive analytic result. The eta allowance
is positive, the density onset precedes the prime-variable onset, and no
uniform joint threshold or all-PV label is asserted. -/
def adaptiveFrontier (η α:ℝ):ℝ :=min (fourFrontier α)
  (α+log α/Real.pi+RHAnalyticFlatPopulation.v1.asymptoticConstant+η)
def adaptive_frontier_curve : Prop :=∀η:ℝ,0<η→∀ᶠα:ℝ in atTop,
  GoodCoefficient α (adaptiveFrontier η α)
/-- Actual prime counts from the hybrid adaptive minimum, with the precise
nested eventual quantifiers. -/
def adaptive_frontier_count : Prop :=∀η:ℝ,0<η→∀ᶠα:ℝ in atTop,
  ∀ᶠx:ℝ in atTop,α*sqrt x<(halfOpenCount (adaptiveFrontier η α) x:ℝ)

end RHWeightedPopulation.v2
