/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectRHHigh
namespace WinnerDirectKernel
open Real IEANTN
set_option maxHeartbeats 0

theorem high_kernel_normalized (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L C : ℝ} (hL : 300 ≤ L)
    (hSpectral : WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8) ≤ C) :
    ‖∑q∈highPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤
        (1+1/1000000000)*C := by
  have hLp : 0 < L := by linarith
  have hv : 0 < (3/4:ℝ)*L := by positivity
  have hvL : (3/4:ℝ)*L ≤ L := by linarith
  have hT : 0 < exp (L/3) := exp_pos _
  have hBound:=high_paired_kernel_bound hqrh hlow hT hv hvL
  have hm:=mul_le_mul_of_nonneg_right hBound (by positivity : 0 ≤ (L/exp L)*exp (L/8))
  have heq : (highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L*
      (exp L*WinnerDensityA.rawSpectral (exp (L/3)) (exp L))/L)*
        ((L/exp L)*exp (L/8))=
      highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L*
        (WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8)) := by
    field_simp [hLp.ne',exp_ne_zero]
  rw [heq] at hm
  have hPaired : 0 ≤ pairedPsiBudget (exp (L/3)) L := by
    unfold pairedPsiBudget
    apply Finset.sum_nonneg
    intro q hq
    have hw:=(pair_properties hqrh hlow hq).1
    positivity
  have hRaw : 0 ≤ WinnerDensityA.rawSpectral (exp (L/3)) (exp L) :=
    nonneg_of_mul_nonneg_right (hPaired.trans (paired_budget_le_raw hT)) (exp_pos L)
  have hFactor:=mul_le_mul_of_nonneg_right (rh_high_factor hL)
    (mul_nonneg hRaw (exp_pos (L/8)).le)
  have hCap:=mul_le_mul_of_nonneg_left hSpectral
    (by norm_num : (0:ℝ) ≤ 1+1/1000000000)
  have hml : ‖∑q∈highPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤
      highFactor (1/8) WinnerOriginalScalars.height ((3/4)*L) L*
        (WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8)) := by
    convert! hm using 1 <;> ring
  exact hml.trans (hFactor.trans hCap)

#print axioms high_kernel_normalized
end WinnerDirectKernel
