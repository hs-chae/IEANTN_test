import IEANTN.Vocabulary.CMSFunctional
import GaussianWings
import GaussianActualFourier

noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory Filter
namespace RHOnePrime.GaussianGap
open RHOnePrime.GaussianKernel RHOnePrime.GaussianFourier IEANTN.CMSFunctional

/-- Every actual function hypothesis, including genuine Fourier association,
is discharged by a proved theorem. No spectral/norm hypothesis remains. -/
theorem gaussian_eligible : Eligible physicalF physicalG where
  continuous := continuous_physicalF
  even := physicalF_even
  integrable := integrable_physicalF
  nonzero := by
    intro h
    have h0 := congrFun h 0
    simp only [Pi.zero_apply] at h0
    have hlo := physicalF_zero_lower
    linarith
  fourier := fourier_actual_physical
  leakage_integrable := by
    simpa only [max_comm] using integrable_physicalG.pos_part.integrableOn

theorem gaussian_denominator_pos : 0 < denominator physicalF physicalG := by
  change 0 < physicalF 0-(36/11 : ℝ)*
    (∫ t in {t : ℝ | 1 < |t|}, max 0 (physicalG t))
  nlinarith [physicalF_zero_lower, physical_full_wings_upper]

theorem gaussian_inverse_upper : inverseObjective physicalF physicalG ≤
    (834021/1000000 : ℝ) := by
  exact physical_full_objective_upper

#print axioms gaussian_eligible
#print axioms gaussian_denominator_pos
#print axioms gaussian_inverse_upper
end RHOnePrime.GaussianGap
