/- Directψ from the original CHJψ source and the actual paired zero sum.
This is independent of the pi conclusion; no extra CH2 analytic source package is used. -/
import SynergyAnalytic.PNTTransfer
namespace SynergyAnalytic
open Real IEANTN WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem paired_zero_sum_norm (qrh : ZetaZeroFreeHalfPlane (7/8))
    (low : LowZeroes.v1.no_zeroes_below_first_ordinate) (T L : ℝ) :
    ‖zeroSum (pairedZeros T) pairZ pairW L‖ ≤ pairedPsiBudget T L := by
  unfold zeroSum pairedPsiBudget
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro q member
  have properties := pair_properties qrh low member
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg properties.1,norm_zexp]
  exact div_le_div_of_nonneg_left (mul_nonneg properties.1 (Real.exp_pos _).le)
    (by linarith [properties.2.2]) (Complex.abs_im_le_norm _)

theorem CHJ_remainder_normalized_tiny {L : ℝ} (domain : 300 ≤ L) :
    ((13/2:ℝ)*L/Real.exp (L/3))*Real.exp (L/8) ≤ 1/100000000 := by
  have positiveL : 0 < L := by linarith
  have main : 0 ≤ ((13/2:ℝ)*L/Real.exp (L/3))*(1/((3/4)*L)) := by positivity
  have early : 0 ≤ 4*L*Real.exp (-(L/4)) := by positivity
  have square : 0 ≤ (L^2+2*L)*Real.exp (-L/2) := by positivity
  have dominate : (13/2:ℝ)*L/Real.exp (L/3) ≤ directRemainder L := by
    unfold directRemainder
    nlinarith
  exact (mul_le_mul_of_nonneg_right dominate (Real.exp_pos _).le).trans
    (direct_remainders_tiny domain)

theorem direct_psi_normalized_of_raw (source : OriginalCHJSource)
    (qrh : ZetaZeroFreeHalfPlane (7/8))
    (low : LowZeroes.v1.no_zeroes_below_first_ordinate)
    {L C : ℝ} (domain : 300 ≤ L)
    (spectral : WinnerDensityA.rawSpectral (Real.exp (L/3)) (Real.exp L)*Real.exp (L/8) ≤ C) :
    Eψ (Real.exp L)*Real.exp (L/8) ≤ C+1/100000000 := by
  have domains := direct_height_domains domain
    (show L ∈ Set.Icc ((3/4)*L) L by constructor <;> linarith)
  have formula := (original_CHJ_to_paired source qrh) L (Real.exp (L/3))
    domains.1 domains.2.1 domains.2.2
  have zeroBound := (Complex.abs_re_le_norm
    (zeroSum (pairedZeros (Real.exp (L/3))) pairZ pairW L)).trans
      ((paired_zero_sum_norm qrh low _ _).trans (paired_budget_le_raw (Real.exp_pos _)))
  have triangle : |psiResidual L| ≤
      |psiResidual L+(zeroSum (pairedZeros (Real.exp (L/3))) pairZ pairW L).re|+
        |(zeroSum (pairedZeros (Real.exp (L/3))) pairZ pairW L).re| := by
    have bound := abs_sub
      (psiResidual L+(zeroSum (pairedZeros (Real.exp (L/3))) pairZ pairW L).re)
      (zeroSum (pairedZeros (Real.exp (L/3))) pairZ pairW L).re
    simpa only [add_sub_cancel_right] using bound
  have total := triangle.trans (add_le_add formula zeroBound)
  have normalized := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right total (Real.exp_pos L).le) (Real.exp_pos (L/8)).le
  have algebra :
      ((13/2:ℝ)*Real.exp L*L/Real.exp (L/3)+
        Real.exp L*WinnerDensityA.rawSpectral (Real.exp (L/3)) (Real.exp L))/Real.exp L=
      (13/2:ℝ)*L/Real.exp (L/3)+WinnerDensityA.rawSpectral (Real.exp (L/3)) (Real.exp L) := by
    field_simp
  rw [algebra,add_mul] at normalized
  change |psiResidual L|/Real.exp L*Real.exp (L/8) ≤ C+1/100000000
  exact (normalized.trans (add_le_add (CHJ_remainder_normalized_tiny domain) spectral)).trans_eq
    (add_comm _ _)

#print axioms paired_zero_sum_norm
#print axioms CHJ_remainder_normalized_tiny
#print axioms direct_psi_normalized_of_raw
end SynergyAnalytic
