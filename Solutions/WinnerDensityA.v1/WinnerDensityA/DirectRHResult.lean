/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectRHSplitNormalized
import WinnerDensityA.LowRHKernel
import WinnerDensityA.HeightResult
namespace WinnerDensityA.HeightRHFinal
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0

/-- Same executed spectral cap, with finite RH used also in the final direct-pi
kernel. All new kernel estimates are ordinary Lean proofs: no new finite facts. -/
theorem source_pi_refined_exact
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ ((1+1/1000000000:ℝ)*(9474448/1000000000)+
      1/1000000000000+1/100000000) 0 (7/8) (exp 300) := by
  apply rh_pi_ray_of_budgets hCHJ hQRH hlow (by norm_num)
  · intro L hL
    exact (WinnerHeightSpectral.height_spectral_ray8192 hrvm hsmall hlow h hRH hQRH hL).trans
      WinnerDensityA.HeightSharpCertificate.coefficient300
  · intro L hL
    exact low_paired_kernel_tiny hQRH hRH hrvm hsmall hlow hL

/-- Upward rounding of the finite-RH-refined direct-pi transfer. -/
theorem source_pi_00947446
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (473723/50000000) 0 (7/8) (exp 300) := by
  intro x hx
  have hh:=source_pi_refined_exact hCHJ hrvm hsmall hlow h hRH hQRH x hx
  have hx0 : 0 < x := (exp_pos _).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num) (rpow_nonneg hx0.le _))

#print axioms source_pi_refined_exact
#print axioms source_pi_00947446
end WinnerDensityA.HeightRHFinal
