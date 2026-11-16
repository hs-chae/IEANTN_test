/- Common mathematical consumer for source-first and strengthened kernel-only routes.
Its finite sum is explicit, allowing the source route to supply the physical output
and the model-only comparator to supply an ordinary kernel computation. -/
import SynergyAnalytic.SourceCountProfile
import SynergyAnalytic.RationalHeightProperties
namespace SynergyAnalytic
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem pi_rational_ray_of_count_caps {a c D : Nat → ℝ} {n : Nat} {C L : ℝ}
    (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
    (last : a n=Real.exp 60) (future : 330 ≤ L)
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤ C)
    (caps : ActualHeightCaps a c D n)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (rationalHeightCoefficient C L) 0 (7/8) (Real.exp L) := by
  have source := source_pi_count_profile_ray monotone first last h caps
    hCHJ hrvm hsmall hlow hRH hQRH future
  have budget := ray_rational_bound weights slopes checked future
  intro x hx
  have positive : 0 < x := (Real.exp_pos L).trans_le hx
  have value := source x hx
  simp only [pow_zero,mul_one] at value ⊢
  exact value.trans (mul_le_mul_of_nonneg_right budget (by positivity))

theorem pi_rational_point_of_count_caps {a c D : Nat → ℝ} {n : Nat} {C x : ℝ}
    (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
    (last : a n=Real.exp 60) (hx : Real.exp 330 ≤ x)
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 77 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤ C)
    (caps : ActualHeightCaps a c D n)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    Eπ x ≤ rationalHeightCoefficient C (Real.log x)*x^(-(1:ℝ)/8) := by
  have positive : 0 < x := (Real.exp_pos 330).trans_le hx
  have future : 330 ≤ Real.log x := by
    have bound := Real.log_le_log (Real.exp_pos 330) hx
    simpa only [Real.log_exp] using bound
  have ray := pi_rational_ray_of_count_caps monotone first last future weights slopes checked caps
    h hCHJ hrvm hsmall hlow hRH hQRH
  have value := ray x (by rw [Real.exp_log positive])
  simpa only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num] using value

#print axioms pi_rational_ray_of_count_caps
#print axioms pi_rational_point_of_count_caps
end SynergyAnalytic
