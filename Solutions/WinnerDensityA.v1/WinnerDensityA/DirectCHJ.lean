/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import WinnerDensityA.DirectZeros
import WinnerDensityA.DirectRayParameters
namespace WinnerDirectKernel
open Real Set MeasureTheory IEANTN
set_option maxHeartbeats 0

/-- Original Cully-Hugill--Johnston arXiv:2111.10001v5 Theorem1.2 Eq1.5,
with alpha=1/2 and the conservative Table4 allowance M=6.5, logx>=40.
The nontrivial-zero sum is written in its standard conjugate-paired form,
with both conjugates and their actual multiplicities at the CLOSED height T.
This is an independently attributed psi explicit-formula source input; it
contains no pi, density, optimized moment, or finite numerical conclusion. -/
def CHJSource : Prop := ∀ u T : ℝ, 40≤u → max 51 u<T → T<(exp (u/2)-2)/2 →
    |psiResidual u+(zeroSum (pairedZeros T) pairZ pairW u).re|≤(13/2)*exp u*u/T

noncomputable def directRemainder (L : ℝ) : ℝ :=
  (13/2)*L/exp (L/3)*(1+1/((3/4)*L))+4*L*exp (-(L/4))+(L^2+2*L)*exp (-L/2)

/-- Actual pi from the original uniform-in-x/T CHJ statement and the already
proved finite-kernel and actual prime-object adapters. -/
theorem actual_pi_from_CHJ (hCHJ : CHJSource)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L : ℝ} (hL : 300≤L) :
    Eπ (exp L)≤highFactor (1/8) 14 ((3/4)*L) L*
      WinnerDensityA.rawSpectral (exp (L/3)) (exp L)+directRemainder L := by
  let v : ℝ := (3/4)*L
  let T : ℝ := exp (L/3)
  have hLp : 0<L := by linarith
  have hv2 : 2≤v := by dsimp [v];linarith
  have hv : 0<v := by linarith
  have hvL : v≤L := by dsimp [v];linarith
  have hT : 0<T := exp_pos _
  have hFormula : ∀u∈Icc v L,
      |psiResidual u+(zeroSum (pairedZeros T) pairZ pairW u).re|≤(13/2)*exp u*u/T := by
    intro u hu
    have hd:=direct_height_domains hL hu
    exact hCHJ u T hd.1 hd.2.1 hd.2.2
  have hResidual:=finite_formula_residual (pairedZeros T) pairZ pairW psiResidual
    (by norm_num : (0:ℝ)≤13/2) hT hv hvL (psi_log_integrable hv hvL) hFormula
  have hKernel:=paired_kernel_bound hqrh hlow hT hv hvL
  have hPi:=actual_Epi_from_logResidual hv2 hvL
  have hSum : |logResidual psiResidual v L|≤
      highFactor (1/8) 14 v L*(exp L*WinnerDensityA.rawSpectral T (exp L))/L+
        ((13/2)*exp L/T)*(1+1/v) := by linarith
  have hPoint := mul_le_mul_of_nonneg_left hSum (by positivity : 0≤L/exp L)
  have he : Eπ (exp L)≤(L/exp L)*
      (highFactor (1/8) 14 v L*(exp L*WinnerDensityA.rawSpectral T (exp L))/L+
        ((13/2)*exp L/T)*(1+1/v)+4*exp v+(L+2)*exp (L/2)) := by
    nlinarith
  have hAexp : exp (-(L/4))=exp v/exp L := by rw [←exp_sub];dsimp [v];congr 1;ring
  have hPexp : exp (-L/2)=exp (L/2)/exp L := by rw [←exp_sub];congr 1;ring
  have hAlg : (L/exp L)*
      (highFactor (1/8) 14 v L*(exp L*WinnerDensityA.rawSpectral T (exp L))/L+
        ((13/2)*exp L/T)*(1+1/v)+4*exp v+(L+2)*exp (L/2)) =
      highFactor (1/8) 14 v L*WinnerDensityA.rawSpectral T (exp L)+directRemainder L := by
    unfold directRemainder
    rw [hAexp,hPexp]
    dsimp [T,v]
    field_simp [hLp.ne',exp_ne_zero]
    <;> ring
  exact he.trans_eq hAlg

 theorem actual_pi_normalized (hCHJ : CHJSource)
    (hqrh : IEANTN.ZetaZeroFreeHalfPlane (7/8))
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L C : ℝ} (hL : 300≤L)
    (hSpectral : WinnerDensityA.rawSpectral (exp (L/3)) (exp L)*exp (L/8)≤C) :
    Eπ (exp L)*exp (L/8)≤(1001/1000:ℝ)*C+1/100000000 := by
  have hT : 0<exp (L/3) := exp_pos _
  have hBudget:=paired_budget_le_raw (L:=L) hT
  have hPaired : 0≤pairedPsiBudget (exp (L/3)) L := by
    unfold pairedPsiBudget
    apply Finset.sum_nonneg
    intro q hq
    have hw:=(pair_properties hqrh hlow hq).1
    positivity
  have hRaw : 0≤WinnerDensityA.rawSpectral (exp (L/3)) (exp L) :=
    nonneg_of_mul_nonneg_right (hPaired.trans hBudget) (exp_pos L)
  have h:=mul_le_mul_of_nonneg_right (actual_pi_from_CHJ hCHJ hqrh hlow hL) (exp_pos (L/8)).le
  have hFactor:=direct_factor_bound hL
  have hTiny:=direct_remainders_tiny hL
  change directRemainder L*exp (L/8)≤1/100000000 at hTiny
  have hFC:=mul_le_mul_of_nonneg_right hFactor
    (mul_nonneg hRaw (exp_pos (L/8)).le)
  have hFinal:=mul_le_mul_of_nonneg_left hSpectral (by norm_num : (0:ℝ)≤1001/1000)
  nlinarith

#print axioms actual_pi_from_CHJ
#print axioms actual_pi_normalized
end WinnerDirectKernel
