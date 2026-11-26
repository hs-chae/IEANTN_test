/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitPopulationWitness
import ExplicitBRPopulationConsumer

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.PopulationWitness
open RH080Next.Explicit

private theorem hlen : 2 ≤ PopulationPV.nodes.length := by rw [PopulationPV.nodes_length]; norm_num
private theorem hlast : node PopulationPV.nodes (PopulationPV.nodes.length-1) = 0 := by
  rw [PopulationPV.nodes_length]
  exact PopulationPV.nodes_terminal

theorem actual_denominator_four : brDenominatorFour PopulationPV.nodes 8 = 1-4*leakage := by
  change amplitude 0-4*IEANTN.CMSFunctional.positiveLeak window = 1-4*leakage
  rw [amplitude_zero,actual_positive_leakage]

theorem window_peak_attained : ∃ v : ℝ, |window v| = maximum := by
  refine ⟨0,?_⟩
  unfold window
  rw [affineSpectrum_zero]
  norm_num [node,PopulationPV.nodes,PopulationPV.Model.coefficients,maximum]

/-- Shared actual-prime population consumer for matched numerical providers. -/
theorem actual_goodCoefficient_of_margin (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1)
    (hperiodic : (∫ y in (0:ℝ)..1, |PopulationPV.Model.trigPolynomial y|) ≤ normCap)
    (c α : ℝ) (hc : 0 < c)
    (hmargin : α < (c*(1-4*leakage)-normCap)/(2*maximum))
    (hRH : RiemannHypothesis) : IEANTN.CMSFunctional.GoodCoefficient α c := by
  have hn : brAmplitudeMass PopulationPV.nodes 8 ≤ normCap :=
    actual_amplitude_norm_le hNorm hperiodic
  apply source_BR_population_goodCoefficient hUniform PopulationPV.nodes 8 (by norm_num)
    hlen (by rw [PopulationPV.nodes_length]; norm_num) hlast maximum
    (by norm_num [maximum]) window_abs_le window_peak_attained
    (by rw [actual_denominator_four]; exact denominator_four_positive) c α hc _ hRH
  rw [actual_denominator_four]
  apply lt_of_lt_of_le hmargin
  exact div_le_div_of_nonneg_right (sub_le_sub_left hn _) (by norm_num [maximum])

theorem actual_population_2108 (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1)
    (hperiodic : (∫ y in (0:ℝ)..1, |PopulationPV.Model.trigPolynomial y|) ≤ normCap)
    (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient 1 (2108/1000:ℝ) :=
  actual_goodCoefficient_of_margin hNorm hUniform hperiodic (2108/1000) 1
    (by norm_num) population_margin_2108 hRH

#print axioms actual_goodCoefficient_of_margin
#print axioms actual_population_2108
end RH080Next.PopulationWitness
