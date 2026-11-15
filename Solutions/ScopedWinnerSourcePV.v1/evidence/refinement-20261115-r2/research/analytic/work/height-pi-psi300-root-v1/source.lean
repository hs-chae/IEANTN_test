/- Complete300ray PNT consumers of the actual zero-sum budget.
Theψproof uses the originalψexplicit formula directly, independently ofπ. -/
import SynergyAnalytic.HeightRawSpectral300
import SynergyAnalytic.DirectPsiSource
namespace SynergyAnalytic
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem pi_300_of_height_caps
    {a c D : Nat → ℝ} {n : Nat}
    (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
    (last : a n=Real.exp 60)
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 0 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤
        8433850764/1000000000000)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (caps : ActualHeightCaps a c D n)
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eπ (9354674/1000000000) 0 (7/8) (Real.exp 300) := by
  have nominal := rh_pi_ray_of_budgets hCHJ hQRH hlow (by norm_num : (300:ℝ)≤300)
    (fun L future=>height_raw_spectral_300 monotone first last weights slopes checked h caps
      hrvm hsmall hlow hRH hQRH (L:=L) future)
    (fun L future=>low_paired_kernel_tiny hQRH hRH hrvm hsmall hlow future)
  intro x hx
  have positiveX : 0 < x := (Real.exp_pos 300).trans_le hx
  have value := nominal x hx
  simp only [pow_zero,mul_one] at value ⊢
  have rounding : ((1+1/1000000000)*(935466375/100000000000)+
      1/1000000000000+1/100000000:ℝ) ≤ 9354674/1000000000 := by norm_num
  exact value.trans (mul_le_mul_of_nonneg_right rounding (Real.rpow_nonneg positiveX.le _))

theorem psi_300_of_height_caps
    {a c D : Nat → ℝ} {n : Nat}
    (monotone : Monotone a) (first : a 0=WinnerOriginalScalars.height)
    (last : a n=Real.exp 60)
    (weights : ∀ i < n, 0 ≤ (1/a i-1/a (i+1))*c i)
    (slopes : ∀ i < n, 0 ≤ D i ∧ D i ≤ 163)
    (checked : 2*(∑ i ∈ Finset.range n,
      ((1/a i-1/a (i+1))*c i)*pairedFactor (D i) (1/8) 330) ≤
        8433850764/1000000000000)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (caps : ActualHeightCaps a c D n)
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eψ (9354674/1000000000) 0 (7/8) (Real.exp 300) := by
  intro x hx
  have positiveX : 0 < x := (Real.exp_pos 300).trans_le hx
  let L := Real.log x
  have future : 300 ≤ L := by
    have compared := Real.log_le_log (Real.exp_pos (300:ℝ)) hx
    simpa only [Real.log_exp] using compared
  have raw := height_raw_spectral_300 monotone first last weights slopes checked h caps
    hrvm hsmall hlow hRH hQRH future
  have normalized := direct_psi_normalized_of_raw hCHJ hQRH hlow future raw
  have heq : Real.exp L=x := Real.exp_log positiveX
  have bound : Eψ (Real.exp L) ≤
      (935466375/100000000000+1/100000000)*Real.exp (-L/8) := by
    have inverse : Real.exp (-L/8)=1/Real.exp (L/8) := by
      rw [show -L/8= -(L/8) by ring,Real.exp_neg,one_div]
    rw [inverse,mul_one_div]
    exact (le_div_iff₀ (Real.exp_pos _)).mpr normalized
  rw [heq] at bound
  have power : x^(-(1:ℝ)/8)=Real.exp (-L/8) := by
    rw [Real.rpow_def_of_pos positiveX]
    dsimp only [L]
    congr 1
    ring
  simp only [pow_zero,mul_one,show (7/8:ℝ)-1= -1/8 by norm_num]
  rw [power]
  exact bound.trans (mul_le_mul_of_nonneg_right (by norm_num :
    (935466375/100000000000+1/100000000:ℝ) ≤ 9354674/1000000000)
      (Real.exp_pos _).le)

#print axioms pi_300_of_height_caps
#print axioms psi_300_of_height_caps
end SynergyAnalytic
