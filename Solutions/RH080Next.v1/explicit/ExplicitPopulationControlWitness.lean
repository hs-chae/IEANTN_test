import ExplicitPopulationANT
import PopulationControl
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RH080Next.PopulationWitness
open RH080Next.Explicit

theorem kernel_only_amplitude_norm_le (hsource : SourceBRFourierNormFive) :
    (∫ u : ℝ, |amplitude u|) ≤ normCap :=
  actual_amplitude_norm_le hsource PopulationPV.kernel_only_periodic_norm

/-- Full actual-pi consumer with the unchanged general literature assumptions.
The numerical provider is kernel-only verification, not source-first PV; no old finite onset is retained. -/
theorem kernel_only_population_2108 (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient 1 (2108/1000:ℝ) :=
  actual_population_2108 hNorm hUniform PopulationPV.kernel_only_periodic_norm hRH

#print axioms kernel_only_population_2108

#print axioms kernel_only_amplitude_norm_le
end RH080Next.PopulationWitness
