import Scaled40ActualConsumers
import PopulationMatchedControl
set_option autoImplicit false
noncomputable section
namespace RH080Exposure.Estimates

theorem gaussian (hCMS : CMSFunctionalInput.v1.population_reduction)
    (hRH : RiemannHypothesis) : RHAsymptoticGaussian.v4.population_curve :=
  RH080Next.Scaled40Canonical.actual_population_curve hCMS hRH

theorem sparse (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    RHWeightedPopulation.v1.sparse_curve :=
  RHWeightedPopulation.v1.challenge_sparse_curve hUniform hRH
    (RH080Next.PopulationCanonical.kernel_only_sparse_witness hNorm)

theorem flat (hNorm : BRFourierInput.v1.norm_identity)
    (hUniform : BRFourierInput.v1.uniform_population_q1) (hRH : RiemannHypothesis) :
    RHWeightedPopulation.v1.flat_curve :=
  RHWeightedPopulation.v1.challenge_flat_curve hUniform hRH
    (RH080Next.PopulationCanonical.kernel_only_flat_witness hNorm)

#print axioms gaussian
#print axioms sparse
#print axioms flat
end RH080Exposure.Estimates
