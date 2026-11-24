import GaussianRays
import GaussianFiniteNorm
import GaussianFiniteWing
import Mathlib.Analysis.Real.Pi.Bounds
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RHOnePrime.GaussianKernel

theorem exp_neg_sixty_upper : Real.exp (-60) ≤ (9/1000000000000000000000000000 : ℝ) := by
  have he := exp_neg_upper_reduction (60 : ℚ) (65066645285712188885243788476446703/166153499473114484112975882535043072 : ℚ)
    (9/1000000000000000000000000000 : ℚ) (by norm_num) 64 24 (by norm_num)
    (by norm_num [Finset.sum_range_succ]) (by norm_num)
  simpa only [Rat.cast_ofNat, Rat.cast_div] using he

theorem norm_tail_integral_upper :
    (∫ u in Ioi (8 : ℝ), radialGaussian true normSource u) ≤ (1/100000000000 : ℝ) := by
  have ht := radialGaussian_infinite_tail true normSource (by decide)
  have hB : 0 ≤ (tailBudget 0 normSource : ℝ) := by exact_mod_cast tailBudget_nonneg normSource 0
  calc
    _ ≤ (tailBudget 0 normSource : ℝ)*Real.exp (-60)*8 := ht
    _ ≤ (tailBudget 0 normSource : ℝ)*(9/1000000000000000000000000000)*8 := by gcongr; exact exp_neg_sixty_upper
    _ ≤ (1/100000000000 : ℝ) := by norm_num [tailBudget, normSource]

theorem wing_tail_integral_upper :
    (∫ u in Ioi (8 : ℝ), radialGaussian false wingSource u) ≤ (1/100000000000 : ℝ) := by
  have ht := radialGaussian_infinite_tail false wingSource (by decide)
  have hB : 0 ≤ (tailBudget 0 wingSource : ℝ) := by exact_mod_cast tailBudget_nonneg wingSource 0
  calc
    _ ≤ (tailBudget 0 wingSource : ℝ)*Real.exp (-60)*8 := ht
    _ ≤ (tailBudget 0 wingSource : ℝ)*(9/1000000000000000000000000000)*8 := by gcongr; exact exp_neg_sixty_upper
    _ ≤ (1/100000000000 : ℝ) := by norm_num [tailBudget, wingSource]

theorem norm_ray_integral_upper :
    (∫ u in Ioi (0 : ℝ), radialGaussian true normSource u) ≤ (66377000001/100000000000 : ℝ) := by
  rw [radialGaussian_ray_split true normSource (by decide) 0 (by norm_num)]
  have hf : (∫ u in (0 : ℝ)..8, radialGaussian true normSource u) ≤ (663770/1000000 : ℝ) :=
    norm_finite_integral
  linarith [norm_tail_integral_upper]

theorem wing_ray_integral_upper :
    (∫ u in Ioi (177245/100000 : ℝ), radialGaussian false wingSource u) ≤ (2760730001/100000000000 : ℝ) := by
  rw [radialGaussian_ray_split false wingSource (by decide) (177245/100000) (by norm_num)]
  have hf : (∫ u in (177245/100000 : ℝ)..8, radialGaussian false wingSource u) ≤ (276073/10000000 : ℝ) :=
    wing_finite_integral
  linarith [wing_tail_integral_upper]

/-- Rational scale bound used for both genuine Gaussian integrals. -/
theorem two_div_sqrt_pi_upper : (2 : ℝ)/Real.sqrt Real.pi ≤ 56419/50000 := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs2 := Real.sq_sqrt Real.pi_pos.le
  apply (div_le_iff₀ hs).mpr
  nlinarith [Real.pi_gt_d6]

theorem wing_start_le_sqrt_pi : (177245/100000 : ℝ) ≤ Real.sqrt Real.pi := by
  have hs : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hs2 := Real.sq_sqrt Real.pi_pos.le
  nlinarith [Real.pi_gt_d6]

#print axioms norm_ray_integral_upper
#print axioms wing_ray_integral_upper
#print axioms two_div_sqrt_pi_upper
end RHOnePrime.GaussianKernel
