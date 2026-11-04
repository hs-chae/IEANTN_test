/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectRHHigh
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0

/-- The actual CHJ-to-prime bridge with its finite kernel left unestimated.
This allows a proved finite-RH split instead of paying a uniform low-height factor. -/
theorem actual_pi_from_CHJ_kernel (hCHJ : CHJSource)
    {L : ℝ} (hL : 300 ≤ L) :
    Eπ (exp L) ≤ (L/exp L)*
      ‖∑q∈pairedZeros (exp (L/3)),(pairW q:ℂ)*piKernel (pairZ q) ((3/4)*L) L‖+
        directRemainder L := by
  let v : ℝ := (3/4)*L
  let T : ℝ := exp (L/3)
  have hLp : 0 < L := by linarith
  have hv2 : 2 ≤ v := by dsimp [v];linarith
  have hv : 0 < v := by linarith
  have hvL : v ≤ L := by dsimp [v];linarith
  have hT : 0 < T := exp_pos _
  have hFormula : ∀u∈Icc v L,
      |psiResidual u+(zeroSum (pairedZeros T) pairZ pairW u).re| ≤ (13/2)*exp u*u/T := by
    intro u hu
    have hd:=direct_height_domains hL hu
    exact hCHJ u T hd.1 hd.2.1 hd.2.2
  have hResidual:=finite_formula_residual (pairedZeros T) pairZ pairW psiResidual
    (by norm_num : (0:ℝ) ≤ 13/2) hT hv hvL (psi_log_integrable hv hvL) hFormula
  have hPi:=actual_Epi_from_logResidual hv2 hvL
  have hSum := mul_le_mul_of_nonneg_left hResidual (by positivity : 0 ≤ L/exp L)
  have he : Eπ (exp L) ≤ (L/exp L)*
      (‖∑q∈pairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L‖+
        ((13/2)*exp L/T)*(1+1/v)+4*exp v+(L+2)*exp (L/2)) := by
    nlinarith
  have hAexp : exp (-(L/4))=exp v/exp L := by rw [←exp_sub];dsimp [v];congr 1;ring
  have hPexp : exp (-L/2)=exp (L/2)/exp L := by rw [←exp_sub];congr 1;ring
  have hAlg : (L/exp L)*
      (‖∑q∈pairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L‖+
        ((13/2)*exp L/T)*(1+1/v)+4*exp v+(L+2)*exp (L/2)) =
      (L/exp L)*‖∑q∈pairedZeros T,(pairW q:ℂ)*piKernel (pairZ q) v L‖+
        directRemainder L := by
    unfold directRemainder
    rw [hAexp,hPexp]
    dsimp [T,v]
    field_simp [hLp.ne',exp_ne_zero]
    <;> ring
  exact he.trans_eq hAlg

/-- A normalized finite-kernel provider gives actual Epi with precisely the
already proved truncation, early-anchor and prime-power budget. -/
theorem actual_pi_normalized_of_kernel (hCHJ : OriginalCHJSource)
    (hqrh : ZetaZeroFreeHalfPlane (7/8)) {L C : ℝ} (hL : 300 ≤ L)
    (hKernel : ‖∑q∈pairedZeros (exp (L/3)),(pairW q:ℂ)*
      piKernel (pairZ q) ((3/4)*L) L‖*(L/exp L)*exp (L/8) ≤ C) :
    Eπ (exp L)*exp (L/8) ≤ C+1/100000000 := by
  have h:=mul_le_mul_of_nonneg_right
    (actual_pi_from_CHJ_kernel (original_CHJ_to_paired hCHJ hqrh) hL) (exp_pos (L/8)).le
  have hTiny:=direct_remainders_tiny hL
  change directRemainder L*exp (L/8) ≤ 1/100000000 at hTiny
  nlinarith

#print axioms actual_pi_normalized_of_kernel
end WinnerDirectKernel
