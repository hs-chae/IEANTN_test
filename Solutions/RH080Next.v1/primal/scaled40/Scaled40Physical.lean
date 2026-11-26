import Scaled40FullRays
import Scaled40Functions
import Scaled40ActualFourier
set_option autoImplicit false
noncomputable section
open scoped BigOperators Interval
open MeasureTheory Set Polynomial
namespace RH080Next.Scaled40
open RH080.Gaussian40

theorem normSource_even (x : ℝ) : coeffEval normSource (-x)=coeffEval normSource x :=
  RH080Next.Scaled40Fourier.normSource_even x

theorem wingSource_even (x : ℝ) : coeffEval wingSource (-x)=coeffEval wingSource x :=
  RH080Next.Scaled40Fourier.wingSource_even x

theorem norm_radial_abs (x : ℝ) : radialGaussian true normSource |x|=radialGaussian true normSource x := by
  by_cases hx : 0≤x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    simp only [radialGaussian, positivePartOrAbs, ite_true, normSource_even, neg_sq]

/-- Exact scaling of the new physical witness's genuine whole-line norm. -/
theorem physical_norm_identity :
    (∫ x : ℝ, |physicalF x|) = ((4/5)*(2/Real.sqrt Real.pi))*
      (∫ u in Ioi (0 : ℝ), radialGaussian true normSource u) := by
  have hpoint (x : ℝ) : |physicalF x| = radialGaussian true normSource
      ((Real.sqrt Real.pi*(5/4))*x) := by
    simp only [physicalF, baseF, radialGaussian, positivePartOrAbs, ite_true,
      abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc]
  simp_rw [hpoint]
  rw [Measure.integral_comp_mul_left]
  have habs := integral_comp_abs (f := radialGaussian true normSource)
  simp_rw [norm_radial_abs] at habs
  rw [habs, smul_eq_mul, abs_of_pos (inv_pos.mpr (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (by norm_num)))]
  field_simp
  <;> ring

theorem physical_norm_upper : (∫ x : ℝ, |physicalF x|) ≤ (7484567744/10000000000 : ℝ) := by
  rw [physical_norm_identity]
  have hs : 0≤(2 : ℝ)/Real.sqrt Real.pi := by positivity
  calc
    _ ≤ ((4/5)*(2/Real.sqrt Real.pi))*(829128182418/1000000000000) :=
      mul_le_mul_of_nonneg_left norm_ray_integral_upper (by positivity)
    _ ≤ ((4/5)*(1128379167096/1000000000000 : ℝ))*(829128182418/1000000000000) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left two_div_sqrt_pi_upper (by norm_num : (0 : ℝ)≤4/5))
        (by norm_num)
    _ ≤ (7484567744/10000000000 : ℝ) := by norm_num

theorem physical_positive_part (x : ℝ) : max 0 (physicalG x) =
    (4/5)*radialGaussian false wingSource ((Real.sqrt Real.pi*(4/5))*x) := by
  unfold physicalG baseG radialGaussian positivePartOrAbs
  simp only [Bool.false_eq_true, ite_false, mul_assoc]
  by_cases hp : 0≤coeffEval wingSource (Real.sqrt Real.pi*(4/5*x))
  · rw [max_eq_right hp, max_eq_right (by positivity)]
  · have hp' : coeffEval wingSource (Real.sqrt Real.pi*(4/5*x))≤0 := le_of_not_ge hp
    rw [max_eq_left hp', max_eq_left (by nlinarith [Real.exp_pos (-((Real.sqrt Real.pi*(4/5*x))^2))])]
    simp

theorem physical_positive_wing_upper :
    2*(∫ x in Ioi (1 : ℝ), max 0 (physicalG x)) ≤ (313227945/10000000000 : ℝ) := by
  simp_rw [physical_positive_part]
  rw [integral_const_mul]
  rw [integral_comp_mul_left_Ioi (radialGaussian false wingSource) 1
    (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (by norm_num))]
  simp only [mul_one, smul_eq_mul]
  have hm : (∫ u in Ioi (Real.sqrt Real.pi*(4/5)), radialGaussian false wingSource u) ≤
      ∫ u in Ioi (354490770181/250000000000 : ℝ), radialGaussian false wingSource u := by
    apply setIntegral_mono_set
      (integrableOn_radialGaussian_ray false wingSource (by decide)
        (354490770181/250000000000) (by norm_num))
      (ae_of_all _ (radialGaussian_nonneg _ _))
    apply ae_of_all
    intro x hx
    have hl : (354490770181/250000000000 : ℝ) ≤ Real.sqrt Real.pi*(4/5) := by
      nlinarith [wing_start_le_sqrt_pi]
    exact lt_of_le_of_lt hl hx
  have he : 2*((4/5)*((Real.sqrt Real.pi*(4/5))⁻¹*
      ∫ u in Ioi (Real.sqrt Real.pi*(4/5)), radialGaussian false wingSource u)) =
      (2/Real.sqrt Real.pi)*(∫ u in Ioi (Real.sqrt Real.pi*(4/5)), radialGaussian false wingSource u) := by
    field_simp
    <;> ring
  rw [he]
  calc
    _ ≤ (2/Real.sqrt Real.pi)*(27759103823/1000000000000) :=
      mul_le_mul_of_nonneg_left (hm.trans wing_ray_integral_upper) (by positivity)
    _ ≤ (1128379167096/1000000000000 : ℝ)*(27759103823/1000000000000) :=
      mul_le_mul_of_nonneg_right two_div_sqrt_pi_upper (by norm_num)
    _ ≤ (313227945/10000000000 : ℝ) := by norm_num

theorem physicalF_zero_exact : physicalF 0=(1 : ℝ) := by
  norm_num [physicalF, baseF, normSource, coeffEval]

#print axioms physical_norm_upper
#print axioms physical_positive_wing_upper
#print axioms physicalF_zero_exact
end RH080Next.Scaled40
