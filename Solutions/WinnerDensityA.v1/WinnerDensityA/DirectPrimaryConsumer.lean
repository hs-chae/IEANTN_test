/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectCHJPairing
namespace WinnerDirectKernel
open Real IEANTN
set_option maxHeartbeats 0

/-- The final pointwise adapter consumes the primary source's ORIGINAL signed
formula. The spectral premise is an intermediate provider discharged by the
existing actual density/grid program in the final application. -/
theorem primary_actual_pi_normalized (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L C : ℝ} (hL : 300≤L)
    (hSpectral : WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8)≤C) :
    Eπ (exp L)*exp (L/8)≤(1001/1000:ℝ)*C+1/100000000 :=
  actual_pi_normalized (original_CHJ_to_paired hCHJ hqrh) hqrh hlow hL hSpectral

/-- Any independently proved actual whole-ray spectral budget feeds the actual
Li2-normalized pi error. It is not a final theorem with a new spectral oracle:
the final application must supply this budget from its source/count program. -/
theorem primary_pi_ray_of_spectral_budget (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L0 C : ℝ} (hL0 : 300≤L0)
    (hBudget : ∀L : ℝ,L0≤L →
      WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8)≤C) :
    HasPowerLogBound Eπ ((1001/1000)*C+1/100000000) 0 (7/8) (exp L0) := by
  intro x hx
  have hx0 : 0<x := (exp_pos L0).trans_le hx
  let L:=log x
  have hL : L0≤L := by
    have hh:=log_le_log (exp_pos L0) hx
    simpa only [log_exp,L] using hh
  have heq : exp L=x := exp_log hx0
  have hh:=primary_actual_pi_normalized hCHJ hqrh hlow (hL0.trans hL) (hBudget L hL)
  rw [heq] at hh
  have hn : Eπ x≤((1001/1000)*C+1/100000000)*exp (-L/8) := by
    have he : exp (-L/8)=1/exp (L/8) := by rw [show -L/8=-(L/8) by ring,exp_neg,one_div]
    rw [he,mul_one_div]
    exact (le_div_iff₀ (exp_pos _)).mpr hh
  simp only [pow_zero,mul_one]
  rw [rpow_def_of_pos hx0]
  have he : log x*((7/8:ℝ)-1)=-L/8 := by dsimp [L];ring
  rw [he]
  exact hn

#print axioms primary_actual_pi_normalized
#print axioms primary_pi_ray_of_spectral_budget
end WinnerDirectKernel
