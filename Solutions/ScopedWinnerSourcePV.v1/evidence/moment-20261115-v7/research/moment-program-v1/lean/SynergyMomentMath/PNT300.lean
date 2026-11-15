/- Strongest shared-mathematics kernel-only consumer of the new exact moments.
No C/source-execution module is imported. Numerical inputs are verified facts,
not additional analytic assumptions; the original14analytic fields stay explicit. -/
import SourceMomentSumsV1.Real
import SynergyMomentMath.Bounds
import SynergyMomentMath.PointCaps
import SynergyAnalytic.MomentAnt300
namespace SynergyMomentMath.PNT300
open ScopedNumerical SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open _root_.Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section

def massUpper : ℝ := 6330434505/1000000000000
def momentUpper : ℝ := 520404202477/1000000000000
def budget300 : ℝ := 1/1000000000000+momentEnvelope massUpper momentUpper 300+momentTail 300

theorem spectral_budget_from_moments
 (mass : totalMass SynergyMomentMath.Real.mass 768 ≤ massUpper)
 (moment : firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768 ≤ momentUpper) :
 spectralBase 300 100+profileCoefficient heightEndpoint
  SynergyMomentMath.Real.cValue SynergyMomentMath.Real.dValue 768 300 ≤ budget300 := by
 have finite:=finiteCoefficient_moment_bound SynergyMomentMath.Bounds.mass_nonnegative
  SynergyMomentMath.Bounds.d_range mass moment (by norm_num : (300:ℝ) ≤ 300)
 change finiteCoefficient (fun i=>2*((1/heightEndpoint i-1/heightEndpoint (i+1))*
  SynergyMomentMath.Real.cValue i)) SynergyMomentMath.Real.dValue 768 300 ≤ _ at finite
 have profile:=profile_of_finite (by norm_num : (300:ℝ) ≤ 300) finite
 have base:=spectralBase_300_tiny
 unfold budget300
 linarith

theorem pi_psi_from_moments
 (mass : totalMass SynergyMomentMath.Real.mass 768 ≤ massUpper)
 (moment : firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768 ≤ momentUpper)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ (8848544/1000000000) 0 (7/8) (Real.exp 300) ∧
 HasPowerLogBound Eψ (8848544/1000000000) 0 (7/8) (Real.exp 300) := by
 have budget:=spectral_budget_from_moments mass moment
 have caps:=PointCaps.actual_caps SourceMomentSumsV1.Real.domains h hRH
 have pi:=pi_300_from_moment_budget heightEndpoint_monotone heightEndpoint_zero
  heightEndpoint_last budget caps h hCHJ hrvm hsmall hlow hRH hQRH
 have psi:=psi_300_from_moment_budget heightEndpoint_monotone heightEndpoint_zero
  heightEndpoint_last budget caps h hCHJ hrvm hsmall hlow hRH hQRH
 have roundedPi : ((1+1/1000000000)*budget300+1/1000000000000+1/100000000:ℝ) ≤
   8848544/1000000000 := by
  norm_num [budget300,momentEnvelope,massUpper,momentUpper,momentTail]
 have roundedPsi : (budget300+1/100000000:ℝ) ≤ 8848544/1000000000 := by
  norm_num [budget300,momentEnvelope,massUpper,momentUpper,momentTail]
 constructor
 · intro x hx
   have positive : 0 < x:=(Real.exp_pos 300).trans_le hx
   have value:=pi x hx
   simp only [pow_zero,mul_one] at value ⊢
   exact value.trans (mul_le_mul_of_nonneg_right roundedPi (by positivity))
 · intro x hx
   have positive : 0 < x:=(Real.exp_pos 300).trans_le hx
   have value:=psi x hx
   simp only [pow_zero,mul_one] at value ⊢
   exact value.trans (mul_le_mul_of_nonneg_right roundedPsi (by positivity))

theorem kernel_pi_psi_300
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ (8848544/1000000000) 0 (7/8) (Real.exp 300) ∧
 HasPowerLogBound Eψ (8848544/1000000000) 0 (7/8) (Real.exp 300) :=
 pi_psi_from_moments SourceMomentSumsV1.Real.mass_bounds.2 SourceMomentSumsV1.Real.moment_upper
  h hCHJ hrvm hsmall hlow hRH hQRH

theorem kernel_pi_future {L : ℝ} (future : 330 ≤ L)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ (finitePNTCoefficient (momentEnvelope massUpper momentUpper L) L)
  0 (7/8) (Real.exp L) := by
 have finite:=finiteCoefficient_moment_bound Bounds.mass_nonnegative Bounds.d_range
  SourceMomentSumsV1.Real.mass_bounds.2 SourceMomentSumsV1.Real.moment_upper
  (by linarith : 300 ≤ L)
 exact pi_ray_of_finite heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
  future finite (PointCaps.actual_caps SourceMomentSumsV1.Real.domains h hRH)
  h hCHJ hrvm hsmall hlow hRH hQRH

theorem strict_old300_coefficient : (8848544/1000000000:ℝ) < 9354674/1000000000 := by norm_num
#print axioms spectral_budget_from_moments
#print axioms pi_psi_from_moments
#print axioms kernel_pi_psi_300
#print axioms kernel_pi_future
#print axioms strict_old300_coefficient
end
end SynergyMomentMath.PNT300
