import ExplicitFlatPopulationANT
import FlatPopulationControl
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace RH080Next.FlatPopulationWitness
open RH080Next.Explicit

theorem kernel_only_population_line (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (α : ℝ) (hα : 0 ≤ α)
    (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient α ((9/8:ℝ)+(16/15:ℝ)*α) :=
  actual_population_line hNorm hUniform FlatPopulationPV.kernel_only_periodic_norm α hα hRH

theorem kernel_only_population_ten (hNorm : SourceBRFourierNormFive)
    (hUniform : SourceBRUniformPopulationQ1) (hRH : RiemannHypothesis) :
    IEANTN.CMSFunctional.GoodCoefficient 10 (283/24:ℝ) :=
  actual_population_ten hNorm hUniform FlatPopulationPV.kernel_only_periodic_norm hRH

#print axioms kernel_only_population_line
#print axioms kernel_only_population_ten
end RH080Next.FlatPopulationWitness
