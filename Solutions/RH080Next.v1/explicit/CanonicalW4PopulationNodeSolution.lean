/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CanonicalW4GlobalNodeSolution
import CanonicalAnalyticFlatNodeSolution
import ExplicitW4StrictPopulation
import WeightedPopulationSolution
import PopulationEnvelopeAlgebra
import IEANTN.Nodes.RHWeightedPopulation.v2.Conclusions
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
open Real IEANTN.CMSFunctional Filter
namespace RHWeightedPopulation.v2

-- The existing seven conclusions remain exact aliases of their v1 meanings.
theorem challenge_sparse_curve (h : RHWeightedPopulation.v1.sparse_curve) : sparse_curve := h
theorem challenge_flat_curve (h : RHWeightedPopulation.v1.flat_curve) : flat_curve := h
theorem challenge_frontier_curve (h : RHWeightedPopulation.v1.frontier_curve) : frontier_curve := h
theorem challenge_frontier_count (h : RHWeightedPopulation.v1.frontier_count) : frontier_count := h
theorem challenge_one_population (h : RHWeightedPopulation.v1.one_population) : one_population := h
theorem challenge_ten_population (h : RHWeightedPopulation.v1.ten_population) : ten_population := h
theorem challenge_below_octic_leading_frontier
    (h : RHWeightedPopulation.v1.below_octic_leading_frontier) : below_octic_leading_frontier := h

/-- Original support7 line, from its actual Mellin/MV pipeline. The norm and
weighted-zero supporting propositions are genuine proof arguments. -/
theorem challenge_w4_curve
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSZeroSummation.v1.partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hNorm : W4FourierNorm.v1.l1_bound)
    (hRH : RiemannHypothesis) : w4_curve := by
  intro α hα
  exact RH080Next.ExplicitProfiles.w4_recorded_population_of_norm
    hStrip hGW hDigamma hPartial hCount hEta hMV hRH hNorm α hα

theorem challenge_w4_infimum_strict
    (hStrip : CMSExplicitInputs.v1.strip_regularity)
    (hGW : CMSExplicitInputs.v1.guinand_weil)
    (hDigamma : CMSExplicitInputs.v1.digamma_integral)
    (hEta : CMSExplicitInputs.v1.real_eta_integral)
    (hCount : CMSExplicitInputs.v1.zero_counting)
    (hPartial : CMSZeroSummation.v1.partial_summation)
    (hMV : CMSExplicitInputs.v1.montgomery_vaughan)
    (hNorm : W4FourierNorm.v1.l1_bound)
    (hRH : RiemannHypothesis) : w4_infimum_strict := by
  intro α hα
  exact RH080Next.ExplicitProfiles.w4_recorded_population_inf_lt_of_norm
    hStrip hGW hDigamma hPartial hCount hEta hMV hRH hNorm α hα

private theorem good_min {α c d : ℝ} (hc : GoodCoefficient α c) (hd : GoodCoefficient α d) :
    GoodCoefficient α (min c d) := by
  rcases le_total c d with h|h
  · simpa only [min_eq_left h] using hc
  · simpa only [min_eq_right h] using hd

theorem challenge_three_frontier_curve (hW4 : w4_curve)
    (hSparse : RHWeightedPopulation.v1.sparse_curve)
    (hFlat : RHWeightedPopulation.v1.flat_curve) : three_frontier_curve := by
  intro α hα
  exact good_min (hW4 α hα) (good_min (hSparse α hα) (hFlat α hα))

theorem challenge_actual_below_both_printed_lines (hCurve : three_frontier_curve) :
    actual_below_both_printed_lines := by
  intro α hα
  refine ⟨threeFrontier α,hCurve α hα,?_⟩
  convert RH080Next.PopulationEnvelope.three_curve_lt_printed_minimum α hα using 1 <;>
    norm_num [threeFrontier,w4Line,RHWeightedPopulation.v1.frontier,
      RHWeightedPopulation.v1.sparseLine,RHWeightedPopulation.v1.flatLine,paperFirst,paperSecond,
      RH080Next.PopulationEnvelope.w4,RH080Next.PopulationEnvelope.sparse,
      RH080Next.PopulationEnvelope.flat,RH080Next.PopulationEnvelope.paperFirst,
      RH080Next.PopulationEnvelope.paperSecond]

theorem challenge_four_frontier_curve (hThree : three_frontier_curve)
    (hAnalytic : RHAnalyticFlatPopulation.v1.flat64_curve) : four_frontier_curve := by
  intro α hα
  exact good_min (hThree α hα) (hAnalytic α hα)

theorem challenge_four_frontier_count (hCurve : four_frontier_curve) : four_frontier_count := by
  intro α hα
  exact RHOnePrime.CMSFunctional.eventual_count_of_good (hCurve α hα)

#print axioms challenge_w4_curve
#print axioms challenge_w4_infimum_strict
#print axioms challenge_three_frontier_curve
#print axioms challenge_actual_below_both_printed_lines
#print axioms challenge_four_frontier_curve
#print axioms challenge_four_frontier_count

theorem challenge_adaptive_frontier_curve (hFour : four_frontier_curve)
    (hAdaptive : RHAnalyticFlatPopulation.v1.adaptive_population) : adaptive_frontier_curve := by
  intro η hη
  filter_upwards [hAdaptive η hη,eventually_gt_atTop (0:ℝ)] with α ha hα
  exact good_min (hFour α hα.le) ha

theorem challenge_adaptive_frontier_count (hCurve : adaptive_frontier_curve) :
    adaptive_frontier_count := by
  intro η hη
  filter_upwards [hCurve η hη] with α ha
  exact RHOnePrime.CMSFunctional.eventual_count_of_good ha

#print axioms challenge_adaptive_frontier_curve
#print axioms challenge_adaptive_frontier_count

end RHWeightedPopulation.v2
