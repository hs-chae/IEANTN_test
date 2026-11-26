import Scaled40Wings
import CMSPopulationFunctionalSource
noncomputable section
set_option autoImplicit false
open Real Set MeasureTheory Filter IEANTN.CMSFunctional
open scoped FourierTransform
namespace RH080Next.Scaled40

theorem integrable_scaledF : Integrable physicalF := by
  exact RH080Next.Scaled40Fourier.integrable_physicalF.comp_mul_left' (by norm_num : (5/4 : ℝ)≠0)

theorem integrable_scaledG : Integrable physicalG := by
  exact (RH080Next.Scaled40Fourier.integrable_physicalG.comp_mul_left' (by norm_num : (4/5 : ℝ)≠0)).const_mul (4/5)

theorem eligible : Eligible physicalF physicalG where
  continuous := RH080Next.Scaled40Fourier.continuous_physicalF.comp (continuous_const.mul continuous_id)
  even := by
    intro x
    simp only [physicalF, mul_neg]
    exact RH080Next.Scaled40Fourier.physicalF_even ((5/4)*x)
  integrable := integrable_scaledF
  nonzero := by
    intro h
    have hz := congrFun h 0
    simp only [Pi.zero_apply] at hz
    rw [physicalF_zero_exact] at hz
    norm_num at hz
  fourier := funext RH080Next.Scaled40Fourier.fourier_scaled_physical
  leakage_integrable := by
    simpa only [max_comm] using integrable_scaledG.pos_part.integrableOn

theorem inverse_objective_upper : inverseObjective physicalF physicalG ≤
    (20582561296/24680948495 : ℝ) := physical_full_objective_upper

theorem eventual_normalized_gap (hCMS : SourceCMSFunctional) (rh : RiemannHypothesis) :
    EventualGapBound (20582561296/24680948495 : ℝ) := by
  have hd : 0<denominator physicalF physicalG := physical_denominator_pos
  exact RHOnePrime.CMSFunctional.bound_mono
    (RHOnePrime.CMSFunctional.gap_from_functional hCMS eligible hd rh)
    inverse_objective_upper

theorem eventual_gap_below_readable (hCMS : SourceCMSFunctional) (rh : RiemannHypothesis) :
    EventualGapBound (833945313/1000000000 : ℝ) :=
  RHOnePrime.CMSFunctional.bound_mono (eventual_normalized_gap hCMS rh) (by norm_num)

theorem eventual_population_curve (hCMS : SourceCMSPopulation) (rh : RiemannHypothesis)
    {α c : ℝ} (hα : 0≤α)
    (hc : (1+2*α)*(20582561296/24680948495 : ℝ)<c) : GoodCoefficient α c := by
  apply RHOnePrime.CMSFunctional.population_from_functional hCMS eligible physical_denominator_pos rh hα
  exact (mul_le_mul_of_nonneg_left inverse_objective_upper (by linarith)).trans_lt hc

#print axioms eligible
#print axioms eventual_normalized_gap
#print axioms eventual_gap_below_readable
#print axioms eventual_population_curve
end RH080Next.Scaled40
