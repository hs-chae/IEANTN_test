import IEANTN.Nodes.GaussianFourierWitness.v1.Conclusions
import GaussianEligibility

noncomputable section
set_option autoImplicit false
open Real MeasureTheory IEANTN.CMSFunctional
namespace GaussianFourierWitness.v1
open RHOnePrime.GaussianKernel RHOnePrime.GaussianGap

/-- The existential is furnished by the actual source-defined polynomial-
Gaussian pair, its genuine Fourier theorem, and whole-real integral proofs. -/
theorem challenge_integral_fourier_witness : integral_fourier_witness := by
  refine ⟨physicalF,physicalG,gaussian_eligible,physical_norm_upper,?_,physicalF_zero_lower⟩
  exact physical_full_wings_upper

/-- Every numerical enclosure in the raw input is used to derive positivity
and the inverse-objective bound. There is no additional numerical premise. -/
theorem challenge_objective_witness (hNumeric : integral_fourier_witness) :
    objective_witness := by
  obtain ⟨F,G,hFG,hmass,hleak,hzero⟩ := hNumeric
  have hd : 0 < denominator F G := by
    unfold denominator
    nlinarith
  refine ⟨F,G,hFG,hd,?_⟩
  unfold inverseObjective
  apply (div_le_iff₀ hd).mpr
  unfold denominator
  nlinarith

#print axioms challenge_integral_fourier_witness
#print axioms challenge_objective_witness
end GaussianFourierWitness.v1
