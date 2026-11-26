/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitNormSourceBridge
import ExplicitCMSEligible
import AffinePopulationBounds
import FlatPopulationNodes

set_option autoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace RH080Next.FlatPopulationWitness
open RH080Next.Explicit

def window : ℝ → ℝ := affineSpectrum FlatPopulationPV.nodes 8
def amplitude : ℝ → ℝ := inverseCosine window
def maximum : ℝ := 533333333333333333/1000000000000000000
def leakage : ℝ := 0
def normCap : ℝ := 1120475208606944546/1000000000000000000
def normalization : ℝ := (15*533333333333333333)/(8*1000000000000000000)

private theorem hlen : 2 ≤ FlatPopulationPV.nodes.length := by rw [FlatPopulationPV.nodes_length]; omega
private theorem hlast : node FlatPopulationPV.nodes (FlatPopulationPV.nodes.length-1) = 0 := by
  rw [FlatPopulationPV.nodes_length]
  exact FlatPopulationPV.nodes_terminal

private theorem all_nodes_bounded (j : ℕ) (hj : j < FlatPopulationPV.nodes.length-1) :
    |node FlatPopulationPV.nodes j| ≤ maximum := by
  rw [FlatPopulationPV.nodes_length] at hj
  interval_cases j <;> norm_num [node,FlatPopulationPV.nodes,FlatPopulationPV.Model.coefficients,maximum]

private theorem outer_nodes_zero (j : ℕ) (hj : 8 < j) : node FlatPopulationPV.nodes j = 0 := by
  by_cases hj17 : j < 17
  · interval_cases j <;> norm_num [node,FlatPopulationPV.nodes,FlatPopulationPV.Model.coefficients] at *
  · unfold node
    rw [List.getD_eq_default _ _ (by rw [FlatPopulationPV.nodes_length]; omega)]
    norm_num

theorem window_abs_le (v : ℝ) : |window v| ≤ maximum :=
  Primal.affineSpectrum_abs_le FlatPopulationPV.nodes 8 maximum hlen (by norm_num [maximum])
    all_nodes_bounded v

theorem actual_positive_leakage : IEANTN.CMSFunctional.positiveLeak window = leakage := by
  unfold IEANTN.CMSFunctional.positiveLeak IEANTN.CMSFunctional.exterior window leakage
  rw [Primal.affineSpectrum_single_boundary_leak FlatPopulationPV.nodes 8 (by norm_num)
    (by rw [FlatPopulationPV.nodes_length]; norm_num) outer_nodes_zero
    (by norm_num [node,FlatPopulationPV.nodes,FlatPopulationPV.Model.coefficients])]
  norm_num [node,FlatPopulationPV.nodes,FlatPopulationPV.Model.coefficients]

@[simp] theorem amplitude_zero : amplitude 0 = normalization := by
  rw [amplitude, inverseCosine_zero, window, integral_affineSpectrum _ 8 (by norm_num),
    FlatPopulationPV.nodal_normalization]
  rfl

theorem actual_eligible : IEANTN.CMSFunctional.Eligible amplitude window :=
  affine_inverse_eligible FlatPopulationPV.nodes 8 hlen (by norm_num) hlast
    (by rw [FlatPopulationPV.nodal_normalization]; norm_num)

/-- Shared mathematical consumer. Source-first and kernel-only numerical
providers enter through the same periodic-norm proposition below. -/
theorem actual_amplitude_norm_le (hsource : SourceBRFourierNormFive)
    (hperiodic : (∫ y in (0:ℝ)..1, |FlatPopulationPV.Model.trigPolynomial y|) ≤ normCap) :
    (∫ u : ℝ, |amplitude u|) ≤ normCap := by
  have heq := affine_norm_eq_periodic_by_padding hsource FlatPopulationPV.nodes 8
    (by norm_num) hlen (by rw [FlatPopulationPV.nodes_length]; norm_num) hlast
  unfold amplitude window
  rw [heq]
  simpa only [FlatPopulationPV.polynomial_identity] using hperiodic

/-- Strict intercept slack with the exact source packet normalization. -/
theorem normalized_norm_strict : normCap < (9/8:ℝ)*normalization := by
  norm_num [normCap,normalization]

theorem population_margin_line (α : ℝ) :
    α < (((9/8:ℝ)+(16/15:ℝ)*α)*normalization-normCap)/(2*maximum) := by
  norm_num [normalization,normCap,maximum]
  linarith

theorem denominator_four_positive : 0 < normalization := by
  norm_num [normalization]

#print axioms window_abs_le
#print axioms actual_positive_leakage
#print axioms actual_eligible
#print axioms actual_amplitude_norm_le
end RH080Next.FlatPopulationWitness
