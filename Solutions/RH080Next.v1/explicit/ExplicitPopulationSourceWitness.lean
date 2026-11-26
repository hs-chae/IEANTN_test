import ExplicitPopulationANT
import PopulationSourceFinal
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RH080Next.PopulationWitness
open RH080Next.Explicit

theorem source_first_amplitude_norm_le (hsource : SourceBRFourierNormFive) :
    (∫ u : ℝ, |amplitude u|) ≤ normCap :=
  actual_amplitude_norm_le hsource PopulationPV.source_first_periodic_norm

/-- Full actual-pi consumer with the unchanged general literature assumptions.
The numerical provider is source-first PV; no old finite onset is retained. -/
theorem source_first_population_2108 (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient 1 (2108/1000:ℝ) :=
  actual_population_2108 hNorm hUniform PopulationPV.source_first_periodic_norm hRH

#print axioms source_first_population_2108

#print axioms source_first_amplitude_norm_le
end RH080Next.PopulationWitness
