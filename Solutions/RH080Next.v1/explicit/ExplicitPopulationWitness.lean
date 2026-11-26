/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitNormSourceBridge
import ExplicitCMSEligible
import AffinePopulationBounds
import PopulationNodes

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.PopulationWitness
open RH080Next.Explicit

def window : ℝ → ℝ := affineSpectrum PopulationPV.nodes 8
def amplitude : ℝ → ℝ := inverseCosine window
def maximum : ℝ := 546871713113309800/1000000000000000000
def leakage : ℝ := 119725872611533800/(8*1000000000000000000)
def normCap : ℝ := 887721072633027910/1000000000000000000

private theorem hlen : 2 ≤ PopulationPV.nodes.length := by rw [PopulationPV.nodes_length]; omega
private theorem hlast : node PopulationPV.nodes (PopulationPV.nodes.length-1) = 0 := by
  rw [PopulationPV.nodes_length]
  exact PopulationPV.nodes_terminal

private theorem all_nodes_bounded (j : ℕ) (hj : j < PopulationPV.nodes.length-1) :
    |node PopulationPV.nodes j| ≤ maximum := by
  rw [PopulationPV.nodes_length] at hj
  interval_cases j <;> norm_num [node,PopulationPV.nodes,PopulationPV.Model.coefficients,maximum]

private theorem outer_nodes_zero (j : ℕ) (hj : 8 < j) : node PopulationPV.nodes j = 0 := by
  by_cases hj17 : j < 17
  · interval_cases j <;> norm_num [node,PopulationPV.nodes,PopulationPV.Model.coefficients] at *
  · unfold node
    rw [List.getD_eq_default _ _ (by rw [PopulationPV.nodes_length]; omega)]
    norm_num

theorem window_abs_le (v : ℝ) : |window v| ≤ maximum :=
  Primal.affineSpectrum_abs_le PopulationPV.nodes 8 maximum hlen (by norm_num [maximum])
    all_nodes_bounded v

theorem actual_positive_leakage : IEANTN.CMSFunctional.positiveLeak window = leakage := by
  unfold IEANTN.CMSFunctional.positiveLeak IEANTN.CMSFunctional.exterior window leakage
  rw [Primal.affineSpectrum_single_boundary_leak PopulationPV.nodes 8 (by norm_num)
    (by rw [PopulationPV.nodes_length]; norm_num) outer_nodes_zero
    (by norm_num [node,PopulationPV.nodes,PopulationPV.Model.coefficients])]
  norm_num [node,PopulationPV.nodes,PopulationPV.Model.coefficients]

@[simp] theorem amplitude_zero : amplitude 0 = 1 := by
  rw [amplitude, inverseCosine_zero, window, integral_affineSpectrum _ 8 (by norm_num),
    PopulationPV.nodal_normalization]

theorem actual_eligible : IEANTN.CMSFunctional.Eligible amplitude window :=
  affine_inverse_eligible PopulationPV.nodes 8 hlen (by norm_num) hlast
    (by rw [PopulationPV.nodal_normalization]; norm_num)

/-- Shared mathematical consumer. Source-first and kernel-only numerical
providers enter through the same periodic-norm proposition below. -/
theorem actual_amplitude_norm_le (hsource : SourceBRFourierNormFive)
    (hperiodic : (∫ y in (0:ℝ)..1, |PopulationPV.Model.trigPolynomial y|) ≤ normCap) :
    (∫ u : ℝ, |amplitude u|) ≤ normCap := by
  have heq := affine_norm_eq_periodic_by_padding hsource PopulationPV.nodes 8
    (by norm_num) hlen (by rw [PopulationPV.nodes_length]; norm_num) hlast
  unfold amplitude window
  rw [heq]
  simpa only [PopulationPV.polynomial_identity] using hperiodic

/-- Exact rational margin for the new alpha=1 population application. The
norm constant is justified by the separately selected numerical provider. -/
theorem population_margin_2108 :
    1 < (((2108/1000:ℝ)*(1-4*leakage)-normCap)/(2*maximum)) := by
  norm_num [leakage,normCap,maximum]

theorem denominator_four_positive : 0 < 1-4*leakage := by
  norm_num [leakage]

#print axioms window_abs_le
#print axioms actual_positive_leakage
#print axioms actual_eligible
#print axioms actual_amplitude_norm_le
end RH080Next.PopulationWitness
