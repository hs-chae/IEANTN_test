/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import AnalyticFlat64Nodes
import AnalyticFlat64Integral
import AnalyticFlat64Log254
import ExplicitCMSEligible

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open Real MeasureTheory RH080Next.Explicit Filter
namespace RH080Next.AnalyticFlat64

/-- Fixed64-flat kernel-only analytic population curve. This is not PV. -/
def width (α : ℝ) : ℝ := 21/10+(128/127)*α

theorem actual_eligible :
    IEANTN.CMSFunctional.Eligible (inverseCosine (affineSpectrum nodes 64))
      (affineSpectrum nodes 64) :=
  affine_inverse_eligible nodes 64 (by rw [nodes_length]; norm_num) (by norm_num)
    (by rw [nodes_length]; exact terminal_zero) (by rw [normalization]; norm_num)

theorem analytic_intercept_strict :
    (2/Real.pi)*(1+log 254)<(21/10:ℝ)*(127/64) := by
  have hlog := log254_lt
  have hpi := Real.pi_gt_d2
  have hnum : 2*(1+log 254)<((21/10:ℝ)*(127/64))*Real.pi := by nlinarith
  calc
    _ = (2*(1+log 254))/Real.pi := by ring
    _ < _ := (div_lt_iff₀ Real.pi_pos).mpr hnum

/-- Actual whole-line Fourier norm from the proved elementary periodic
integral and the already explicit general BR analytic norm identity. -/
theorem actual_norm_strict (hNorm : SourceBRFourierNormFive) :
    brAmplitudeMass nodes 64<(21/10:ℝ)*(127/64) := by
  have heq := hNorm nodes 64 (by norm_num)
    (by rw [nodes_length]) terminal_zero
  unfold brAmplitudeMass
  rw [heq]
  simp_rw [polynomial_identity]
  exact periodic_norm_bound.trans_lt analytic_intercept_strict

/-- Under the same literal BR norm and q=1 population propositions and RH,
the actual prime counting function has this strict eventual population
margin for every nonnegative alpha. No numerical result or source program
is assumed or verified on this pure analytic route. -/
theorem actual_population_curve (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (α : ℝ) (hα : 0≤α) : IEANTN.CMSFunctional.GoodCoefficient α (width α) := by
  apply source_BR_population_goodCoefficient hUniform nodes 64 (by norm_num)
    (by rw [nodes_length]; norm_num) (by rw [nodes_length])
    (by rw [nodes_length]; exact terminal_zero) 1 (by norm_num) window_bound
    attained_maximum (by rw [denominator]; norm_num) (width α) α
    (by unfold width; linarith) _ hRH
  rw [denominator]
  have hn := actual_norm_strict hNorm
  unfold width
  nlinarith

/-- Explicit statement about the actual half-open prime count. The positive
margin retains the published strict liminf form; no finite onset is claimed. -/
theorem actual_population_eventual (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis)
    (α : ℝ) (hα : 0≤α) :
    ∃δ:ℝ,0<δ ∧ ∀ᶠ x:ℝ in atTop,
      (α+δ)*sqrt x≤(IEANTN.CMSFunctional.halfOpenCount (width α) x:ℝ) := by
  rcases (actual_population_curve hNorm hUniform hRH α hα).2 with ⟨δ,hδ,hevent⟩
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hevent,eventually_gt_atTop (0:ℝ)] with x hx hx0
  unfold IEANTN.CMSFunctional.normalizedPopulation at hx
  exact (le_div_iff₀ (sqrt_pos.2 hx0)).mp hx

theorem width_forty : width 40=(53867:ℝ)/1270 := by norm_num [width]

theorem actual_population_forty (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient 40 ((53867:ℝ)/1270) := by
  rw [←width_forty]
  exact actual_population_curve hNorm hUniform hRH 40 (by norm_num)


/-- Exact comparison with the previously completed flat16 line. This is not
an optimality or best-known-result assertion. -/
theorem improves_previous_flat (α : ℝ) (hα : (14859:ℝ)/896<α) :
    width α<(9/8:ℝ)+(16/15:ℝ)*α := by unfold width; linarith

theorem forty_improves_previous_flat : width 40<(9/8:ℝ)+(16/15:ℝ)*40 := by
  norm_num [width]

#print axioms actual_eligible
#print axioms analytic_intercept_strict
#print axioms actual_norm_strict
#print axioms actual_population_curve
#print axioms actual_population_eventual
#print axioms actual_population_forty
end RH080Next.AnalyticFlat64
