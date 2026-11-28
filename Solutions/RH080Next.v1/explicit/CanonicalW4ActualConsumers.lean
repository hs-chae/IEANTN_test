/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CanonicalW4NormNodeSolution
import CanonicalW4PopulationNodeSolution
import CanonicalFiniteNodeSolution
import PopulationActualConsumers
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.CanonicalW4
open Real

section LiteralInputs
variable (hBRNorm : BRFourierInput.v1.norm_identity)
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hRH : RiemannHypothesis)
include hBRNorm hStrip hGW hDigamma hEta hCount hMV hRH

/-- Closed numerical/zero supporting nodes, with the literal analytic,
historical computation and RH inputs preserved. Actual W4 C main is consumed. -/
theorem source_first_global (hGap : CMSExplicitInputs.v1.historical_finite_gap) :
    RHGlobalAffineIntervals.v1.global_0851062 :=
  RHGlobalAffineIntervals.v1.challenge_global_0851062
    hStrip hGW hDigamma hEta hCount CMSZeroSummation.v1.challenge_partial_summation
    hMV hGap (W4FourierNorm.v1.challenge_l1_bound hBRNorm) hRH

theorem source_first_five_branches (hGap : CMSExplicitInputs.v1.historical_finite_gap) :
    RHGlobalAffineIntervals.v1.branch_0777 ∧ RHGlobalAffineIntervals.v1.branch_074 ∧
    RHGlobalAffineIntervals.v1.branch_075 ∧ RHGlobalAffineIntervals.v1.branch_08 ∧
    RHGlobalAffineIntervals.v1.branch_0851062 := by
  refine ⟨RHGlobalAffineIntervals.v1.challenge_branch_0777
    RHFiniteAffineIntervals.v2.challenge_interval_0777_small,?_,?_,?_,?_⟩
  · exact RHGlobalAffineIntervals.v1.challenge_branch_074
      (CanonicalEvolution.source_first_interval_074_full
        hStrip hGW hDigamma hEta hCount hMV hGap hBRNorm hRH)
  · exact RHGlobalAffineIntervals.v1.challenge_branch_075
      (CanonicalEvolution.source_first_interval_075_full
        hStrip hGW hDigamma hEta hCount hMV hGap hBRNorm hRH)
  · exact RHGlobalAffineIntervals.v1.challenge_branch_08
      (CanonicalEvolution.source_first_interval_08_full
        hStrip hGW hDigamma hEta hCount hMV hGap hBRNorm hRH)
  · exact RHGlobalAffineIntervals.v1.challenge_branch_0851062
      (source_first_global hBRNorm hStrip hGW hDigamma hEta hCount hMV hRH hGap)

theorem source_first_piecewise (hGap : CMSExplicitInputs.v1.historical_finite_gap) :
    RHGlobalAffineIntervals.v1.piecewise_strict := by
  obtain ⟨h0,h1,h2,h3,h4⟩:=source_first_five_branches
    hBRNorm hStrip hGW hDigamma hEta hCount hMV hRH hGap
  exact RHGlobalAffineIntervals.v1.challenge_piecewise_strict h0 h1 h2 h3 h4

theorem source_first_w4_curve : RHWeightedPopulation.v2.w4_curve :=
  RHWeightedPopulation.v2.challenge_w4_curve hStrip hGW hDigamma hEta hCount
    CMSZeroSummation.v1.challenge_partial_summation hMV
    (W4FourierNorm.v1.challenge_l1_bound hBRNorm) hRH

theorem source_first_w4_infimum_strict : RHWeightedPopulation.v2.w4_infimum_strict :=
  RHWeightedPopulation.v2.challenge_w4_infimum_strict hStrip hGW hDigamma hEta hCount
    CMSZeroSummation.v1.challenge_partial_summation hMV
    (W4FourierNorm.v1.challenge_l1_bound hBRNorm) hRH

/-- All three actual source-first numerical providers, under their common
ordinary-RH premises. The source q1 input belongs to the two short profiles;
the W4 branch uses its own support7 Mellin/MV derivation. -/
theorem source_first_three_frontier (hUniform : BRFourierInput.v1.uniform_population_q1) :
    RHWeightedPopulation.v2.three_frontier_curve := by
  apply RHWeightedPopulation.v2.challenge_three_frontier_curve
    (source_first_w4_curve hBRNorm hStrip hGW hDigamma hEta hCount hMV hRH)
  · intro α hα
    exact PopulationCanonical.source_first_sparse_curve hBRNorm hUniform hRH α hα
  · intro α hα
    exact PopulationCanonical.source_first_flat_curve hBRNorm hUniform hRH α hα

/-- A hybrid consumer: actual numerical C programs plus a kernel-only
analytic fixed64 component. The hybrid is not labeled entirely PV. -/
theorem hybrid_four_frontier (hUniform : BRFourierInput.v1.uniform_population_q1) :
    RHWeightedPopulation.v2.four_frontier_curve :=
  RHWeightedPopulation.v2.challenge_four_frontier_curve
    (source_first_three_frontier hBRNorm hStrip hGW hDigamma hEta hCount hMV hRH hUniform)
    (RHAnalyticFlatPopulation.v1.challenge_flat64_curve hBRNorm hUniform hRH)

/-- Density first, prime-variable onset second; no uniform joint onset. -/
theorem hybrid_adaptive_frontier (hUniform : BRFourierInput.v1.uniform_population_q1) :
    RHWeightedPopulation.v2.adaptive_frontier_curve := by
  apply RHWeightedPopulation.v2.challenge_adaptive_frontier_curve
    (hybrid_four_frontier hBRNorm hStrip hGW hDigamma hEta hCount hMV hRH hUniform)
  exact RHAnalyticFlatPopulation.v1.challenge_adaptive_population
    (RHAnalyticFlatPopulation.v1.challenge_family_curve hBRNorm hUniform hRH)
    RHAnalyticFlatPopulation.v1.challenge_adaptive_limit

theorem hybrid_adaptive_count (hUniform : BRFourierInput.v1.uniform_population_q1) :
    RHWeightedPopulation.v2.adaptive_frontier_count :=
  RHWeightedPopulation.v2.challenge_adaptive_frontier_count
    (hybrid_adaptive_frontier hBRNorm hStrip hGW hDigamma hEta hCount hMV hRH hUniform)
end LiteralInputs

end RH080Next.CanonicalW4
