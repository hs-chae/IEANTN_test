/- Copyright (c)2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.HeightSpectral
import WinnerDensityA.HeightSharpCertificate
import WinnerDensityA.DirectPrimaryConsumer
namespace WinnerDensityA.HeightFinal
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0

/-- Independent final assembly: every new numerical and spectral budget is
supplied by its executed-and-proved provider. Only original source inputs,
original-height finite RH and QRH remain as hypotheses. -/
theorem source_pi_exact
    (hCHJ:OriginalCHJSource)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ ((1001/1000:ℝ)*(9474448/1000000000)+1/100000000) 0 (7/8) (exp 300) := by
  apply primary_pi_ray_of_spectral_budget hCHJ hQRH hlow (by norm_num)
  intro L hL
  exact (WinnerHeightSpectral.height_spectral_ray8192 hrvm hsmall hlow h hRH hQRH hL).trans
    WinnerDensityA.HeightSharpCertificate.coefficient300

/-- Convenient upward decimal rounding of the independently assembled result. -/
theorem source_pi_009484
    (hCHJ:OriginalCHJSource)
    (hrvm:ZeroCount.v1.rvm_error_bound) (hsmall:ZeroCount.v1.rvm_error_small)
    (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h:WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (2371/250000) 0 (7/8) (exp 300) := by
  intro x hx
  have hh:=source_pi_exact hCHJ hrvm hsmall hlow h hRH hQRH x hx
  have hx0:0<x:=(exp_pos _).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num) (rpow_nonneg hx0.le _))
#print axioms source_pi_exact
#print axioms source_pi_009484
#check source_pi_009484
end WinnerDensityA.HeightFinal
