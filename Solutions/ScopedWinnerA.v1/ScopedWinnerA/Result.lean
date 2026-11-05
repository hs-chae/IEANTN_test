/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedWinnerA.Certificate
import WinnerDensityA.DirectRHResult
namespace ScopedWinnerA
open Real IEANTN WinnerDirectKernel
set_option maxHeartbeats 0
/-- Same original seven inputs and analytic transfer; only the executed sigma grid changed. -/
theorem pi_refined_exact
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ ((1+1/1000000000:ℝ)*(9471452/1000000000)+
      1/1000000000000+1/100000000) 0 (7/8) (exp 300) := by
  apply rh_pi_ray_of_budgets hCHJ hQRH hlow (by norm_num)
  · intro L hL
    exact (WinnerHeightSpectral.height_spectral_ray hrvm hsmall hlow h hRH hQRH
      (by norm_num : 0<(16384:ℕ)) hL).trans Certificate.coefficient300
  · intro L hL
    exact low_paired_kernel_tiny hQRH hRH hrvm hsmall hlow hL
/-- New actual prime-counting bound; the output of a genuine interval execution is consumed. -/
theorem pi_00947147
    (hCHJ : OriginalCHJSource)
    (hrvm : ZeroCount.v1.rvm_error_bound) (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (h : WinnerNewHeightSource.PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (947147/100000000) 0 (7/8) (exp 300) := by
  intro x hx
  have hh:=pi_refined_exact hCHJ hrvm hsmall hlow h hRH hQRH x hx
  have hx0 : 0<x := (exp_pos _).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num) (rpow_nonneg hx0.le _))
#print axioms pi_00947147
end ScopedWinnerA
