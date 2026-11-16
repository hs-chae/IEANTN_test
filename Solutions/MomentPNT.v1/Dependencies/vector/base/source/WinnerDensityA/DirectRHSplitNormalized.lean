/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectRHPiKernel
import WinnerDensityA.DirectRHHighNormalized
namespace WinnerDirectKernel
open Real IEANTN
set_option maxHeartbeats 0

/-- The finite low/high partition consumes the actual low-kernel provider;
the final theorem discharges it from finite RH and the original reciprocal sum. -/
theorem rh_split_actual_pi_normalized (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L C epsilon : ℝ} (hL : 300 ≤ L)
    (hSpectral : WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8) ≤ C)
    (hLowKernel : ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤ epsilon) :
    Eπ (exp L)*exp (L/8) ≤ (1+1/1000000000)*C+epsilon+1/100000000 := by
  have hHigh:=high_kernel_normalized hqrh hlow hL hSpectral
  have hNorm:=norm_add_le
    (∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L)
    (∑q∈highPairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L)
  rw [←split_paired_kernel] at hNorm
  have hLp : 0 < L := by linarith
  have hMult:=mul_le_mul_of_nonneg_right hNorm
    (by positivity : 0 ≤ (L/exp L)*exp (L/8))
  have hKernel : ‖∑q∈pairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤
        (1+1/1000000000)*C+epsilon := by
    nlinarith only [hMult,hHigh,hLowKernel]
  exact actual_pi_normalized_of_kernel hCHJ hqrh hL hKernel

/-- Whole-ray adapter; both numerical and finite-RH providers are discharged
by the independently proved source lemmas in the final application. -/
theorem rh_pi_ray_of_budgets (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L0 C epsilon : ℝ} (hL0 : 300 ≤ L0)
    (hBudget : ∀L : ℝ,L0 ≤ L →
      WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8) ≤ C)
    (hLow : ∀L : ℝ,L0 ≤ L → ‖∑q∈lowPairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤ epsilon) :
    HasPowerLogBound Eπ ((1+1/1000000000)*C+epsilon+1/100000000) 0 (7/8) (exp L0) := by
  intro x hx
  have hx0 : 0 < x := (exp_pos L0).trans_le hx
  let L:=log x
  have hL : L0 ≤ L := by
    have hh:=log_le_log (exp_pos L0) hx
    simpa only [log_exp,L] using hh
  have heq : exp L=x := exp_log hx0
  have hh:=rh_split_actual_pi_normalized hCHJ hqrh hlow (hL0.trans hL)
    (hBudget L hL) (hLow L hL)
  rw [heq] at hh
  have hn : Eπ x ≤ ((1+1/1000000000)*C+epsilon+1/100000000)*exp (-L/8) := by
    have he : exp (-L/8)=1/exp (L/8) := by rw [show -L/8=-(L/8) by ring,exp_neg,one_div]
    rw [he,mul_one_div]
    exact (le_div_iff₀ (exp_pos _)).mpr hh
  simp only [pow_zero,mul_one]
  rw [rpow_def_of_pos hx0]
  have he : log x*((7/8:ℝ)-1)=-L/8 := by dsimp [L];ring
  rw [he]
  exact hn

#print axioms rh_split_actual_pi_normalized
#print axioms rh_pi_ray_of_budgets
end WinnerDirectKernel
