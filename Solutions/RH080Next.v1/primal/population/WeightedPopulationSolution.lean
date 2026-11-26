/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import BRSourceInterfaces
import CMSPopulationFunctionalSource
import PopulationFrontierComparison

set_option autoImplicit false
noncomputable section
open Real Set Filter MeasureTheory IEANTN.CMSFunctional
namespace RHWeightedPopulation.v1
open RH080Next.Explicit AffineFourierPrograms.v1

/-- This consumer imports only the witness proposition, so source-first and
matched kernel-only providers face exactly the same mathematical inference. -/
theorem challenge_sparse_curve
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) (hProvider : sparse_witness) : sparse_curve := by
  rcases hProvider with ⟨hEligible,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour sparseNodes 8 =
      1-4*(119725872611533800/(8*1000000000000000000) : ℝ) := by
    change sparseAmplitude 0-4*positiveLeak sparseWindow = _
    rw [h0,hJ]
  have hN' : brAmplitudeMass sparseNodes 8 ≤
      (887721072633027910/1000000000000000000 : ℝ) := hN
  intro α hα
  apply source_BR_population_goodCoefficient hUniform sparseNodes 8 (by norm_num)
    (by decide) (by decide)
    (by norm_num [node,sparseNodes,sparseNumerators])
    (546871713113309800/1000000000000000000 : ℝ)
    (by norm_num) hBound hAttain (by rw [hD]; norm_num) (sparseLine α) α
    (by dsimp [sparseLine]; positivity) _ hRH
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*(546871713113309800/1000000000000000000))).2
  have hMargin :
      2*(546871713113309800/1000000000000000000 : ℝ)*α <
        sparseLine α*(1-4*(119725872611533800/(8*1000000000000000000) : ℝ))-
          (887721072633027910/1000000000000000000 : ℝ) := by
    dsimp [sparseLine]
    nlinarith
  linarith

theorem challenge_flat_curve
    (hUniform : BRFourierInput.v1.uniform_population_q1)
    (hRH : RiemannHypothesis) (hProvider : flat_witness) : flat_curve := by
  rcases hProvider with ⟨hEligible,hN,hJ,h0,hBound,hAttain⟩
  have hD : brDenominatorFour flatNodes 8 =
      ((15*533333333333333333)/(8*1000000000000000000) : ℝ) := by
    change flatAmplitude 0-4*positiveLeak flatWindow = _
    rw [h0,hJ]; ring
  have hN' : brAmplitudeMass flatNodes 8 ≤
      (1120475208606944546/1000000000000000000 : ℝ) := hN
  intro α hα
  apply source_BR_population_goodCoefficient hUniform flatNodes 8 (by norm_num)
    (by decide) (by decide)
    (by norm_num [node,flatNodes,flatNumerators])
    (533333333333333333/1000000000000000000 : ℝ)
    (by norm_num) hBound hAttain (by rw [hD]; norm_num) (flatLine α) α
    (by dsimp [flatLine]; positivity) _ hRH
  rw [hD]
  apply (lt_div_iff₀ (by norm_num : (0:ℝ)<2*(533333333333333333/1000000000000000000))).2
  have hMargin :
      2*(533333333333333333/1000000000000000000 : ℝ)*α <
        flatLine α*((15*533333333333333333)/(8*1000000000000000000) : ℝ)-
          (1120475208606944546/1000000000000000000 : ℝ) := by
    dsimp [flatLine]
    nlinarith
  linarith

theorem challenge_frontier_curve (hSparse : sparse_curve) (hFlat : flat_curve) :
    frontier_curve := by
  intro α hα
  rcases le_total (sparseLine α) (flatLine α) with h | h
  · simpa only [frontier,min_eq_left h] using hSparse α hα
  · simpa only [frontier,min_eq_right h] using hFlat α hα

theorem challenge_frontier_count (hFrontier : frontier_curve) : frontier_count := by
  intro α hα
  exact RHOnePrime.CMSFunctional.eventual_count_of_good (hFrontier α hα)

theorem challenge_one_population (hSparse : sparse_curve) : one_population := by
  apply RHOnePrime.CMSFunctional.goodCoefficient_mono (hSparse 1 (by norm_num))
  norm_num [sparseLine]

theorem challenge_ten_population (hFlat : flat_curve) : ten_population := by
  change GoodCoefficient 10 (283/24 : ℝ)
  simpa only [flatLine,show (9/8:ℝ)+(16/15:ℝ)*10=283/24 by norm_num] using
    hFlat 10 (by norm_num)

theorem challenge_below_octic_leading_frontier : below_octic_leading_frontier := by
  intro α _
  exact RH080Next.Primal.new_frontier_lt_octic α

#print axioms challenge_sparse_curve
#print axioms challenge_flat_curve
#print axioms challenge_frontier_curve
#print axioms challenge_frontier_count
#print axioms challenge_one_population
#print axioms challenge_ten_population
#print axioms challenge_below_octic_leading_frontier
end RHWeightedPopulation.v1
