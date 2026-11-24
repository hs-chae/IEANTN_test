import IEANTN.Nodes.CMSFunctionalInput.v1.Conclusions
import IEANTN.Nodes.GaussianFourierWitness.v1.Conclusions
import IEANTN.Nodes.RHAsymptoticGaussian.v1.Conclusions
import IEANTN.Nodes.RH.v1.Conclusions
import CMSPopulationFunctionalSource

noncomputable section
set_option autoImplicit false
open Real MeasureTheory Filter IEANTN.CMSFunctional
namespace RHAsymptoticGaussian.v1
open RHOnePrime.CMSFunctional

/-- The actual numerical-node argument is consumed; no Gaussian numerical
proof is recomputed behind an unused input in this general ANT consumer. -/
theorem challenge_normalized_gap (hCMS : CMSFunctionalInput.v1.gap_reduction)
    (rh : RH.v1.hypothesis) (hNumeric : GaussianFourierWitness.v1.objective_witness) :
    normalized_gap := by
  obtain ⟨F,G,hFG,hd,hq⟩ := hNumeric
  exact bound_mono (gap_from_functional hCMS hFG hd rh) hq

theorem challenge_gap_below_printed_2026 (hgap : normalized_gap) :
    gap_below_printed_2026 := by
  have h := hgap (29619151/2000000000000) (by norm_num)
  filter_upwards [h] with n hn
  linarith

theorem challenge_population_curve (hCMS : CMSFunctionalInput.v1.population_reduction)
    (rh : RH.v1.hypothesis) (hNumeric : GaussianFourierWitness.v1.objective_witness) :
    population_curve := by
  obtain ⟨F,G,hFG,hd,hq⟩ := hNumeric
  intro α hα ε hε
  apply population_from_functional hCMS hFG hd rh hα
  have hsum : 0 ≤ 1+2*α := by linarith
  have hm := mul_le_mul_of_nonneg_left hq hsum
  nlinarith

theorem challenge_population_count (hcurve : population_curve) : population_count := by
  intro α hα ε hε
  exact eventual_count_of_good (hcurve α hα ε hε)

#print axioms challenge_normalized_gap
#print axioms challenge_gap_below_printed_2026
#print axioms challenge_population_curve
#print axioms challenge_population_count
end RHAsymptoticGaussian.v1
