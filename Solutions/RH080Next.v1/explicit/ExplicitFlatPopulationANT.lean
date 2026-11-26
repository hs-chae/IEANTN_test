/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFlatPopulationWitness
import ExplicitBRPopulationConsumer

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.FlatPopulationWitness
open RH080Next.Explicit

private theorem hlen : 2 ≤ FlatPopulationPV.nodes.length := by rw [FlatPopulationPV.nodes_length]; norm_num
private theorem hlast : node FlatPopulationPV.nodes (FlatPopulationPV.nodes.length-1) = 0 := by
  rw [FlatPopulationPV.nodes_length]
  exact FlatPopulationPV.nodes_terminal

theorem actual_denominator_four : brDenominatorFour FlatPopulationPV.nodes 8 = normalization := by
  change amplitude 0-4*IEANTN.CMSFunctional.positiveLeak window = normalization
  rw [amplitude_zero,actual_positive_leakage]
  norm_num [leakage]

theorem window_peak_attained : ∃ v : ℝ, |window v| = maximum := by
  refine ⟨0,?_⟩
  unfold window
  rw [affineSpectrum_zero]
  norm_num [node,FlatPopulationPV.nodes,FlatPopulationPV.Model.coefficients,maximum]

/-- Shared actual-prime population consumer for matched numerical providers. -/
theorem actual_goodCoefficient_of_margin (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1)
    (hperiodic : (∫ y in (0:ℝ)..1, |FlatPopulationPV.Model.trigPolynomial y|) ≤ normCap)
    (c α : ℝ) (hc : 0 < c)
    (hmargin : α < (c*normalization-normCap)/(2*maximum))
    (hRH : RiemannHypothesis) : IEANTN.CMSFunctional.GoodCoefficient α c := by
  have hn : brAmplitudeMass FlatPopulationPV.nodes 8 ≤ normCap :=
    actual_amplitude_norm_le hNorm hperiodic
  apply source_BR_population_goodCoefficient hUniform FlatPopulationPV.nodes 8 (by norm_num)
    hlen (by rw [FlatPopulationPV.nodes_length]; norm_num) hlast maximum
    (by norm_num [maximum]) window_abs_le window_peak_attained
    (by rw [actual_denominator_four]; exact denominator_four_positive) c α hc _ hRH
  rw [actual_denominator_four]
  apply lt_of_lt_of_le hmargin
  exact div_le_div_of_nonneg_right (sub_le_sub_left hn _) (by norm_num [maximum])

theorem actual_population_line (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1)
    (hperiodic : (∫ y in (0:ℝ)..1, |FlatPopulationPV.Model.trigPolynomial y|) ≤ normCap)
    (α : ℝ) (hα : 0 ≤ α) (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient α ((9/8:ℝ)+(16/15:ℝ)*α) :=
  actual_goodCoefficient_of_margin hNorm hUniform hperiodic _ α (by linarith)
    (population_margin_line α) hRH

theorem actual_population_ten (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1)
    (hperiodic : (∫ y in (0:ℝ)..1, |FlatPopulationPV.Model.trigPolynomial y|) ≤ normCap)
    (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient 10 (283/24:ℝ) := by
  simpa only [show (9/8:ℝ)+(16/15:ℝ)*10 = 283/24 by norm_num] using
    actual_population_line hNorm hUniform hperiodic 10 (by norm_num) hRH

#print axioms actual_goodCoefficient_of_margin
#print axioms actual_population_line
#print axioms actual_population_ten
end RH080Next.FlatPopulationWitness
