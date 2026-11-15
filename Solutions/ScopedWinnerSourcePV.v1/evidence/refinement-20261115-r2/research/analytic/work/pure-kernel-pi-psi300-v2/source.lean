/- Earlier-onset current-input results from the campaign's verified pure data.
This is not the original four-input/all12row legacy frontier contract. -/
import SynergyAnalytic.HeightPiPsi300
import SynergyAnalytic.PureKernelHeightGuards
namespace SynergyAnalytic.HeightPoint.PureKernelPiPsi300
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem pi_300
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eπ (9354674/1000000000) 0 (7/8) (Real.exp 300) :=
  pi_300_of_height_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
    PureKernelHeightGuards.weights_nonnegative
    (fun i hi=>⟨(by norm_num : (0:ℝ)≤77).trans (PureKernelHeightGuards.slope_range hi).1,
      (PureKernelHeightGuards.slope_range hi).2⟩)
    finite_height_budget_tight h (actual_height_cells h hRH) hCHJ hrvm hsmall hlow hRH hQRH

theorem psi_300
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eψ (9354674/1000000000) 0 (7/8) (Real.exp 300) :=
  psi_300_of_height_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
    PureKernelHeightGuards.weights_nonnegative
    (fun i hi=>⟨(by norm_num : (0:ℝ)≤77).trans (PureKernelHeightGuards.slope_range hi).1,
      (PureKernelHeightGuards.slope_range hi).2⟩)
    finite_height_budget_tight h (actual_height_cells h hRH) hCHJ hrvm hsmall hlow hRH hQRH

/-- Same numeric300target as the legacy row, under CURRENT fourteen inputs only.
No assertion of the originalall12row frontier or its different input-map closure. -/
theorem psi_01310_current_inputs
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) : HasPowerLogBound Eψ (131/10000) 0 (7/8) (Real.exp 300) := by
  have source := psi_300 h hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have positiveX : 0 < x := (Real.exp_pos 300).trans_le hx
  have value := source x hx
  simp only [pow_zero,mul_one] at value ⊢
  exact value.trans (mul_le_mul_of_nonneg_right (by norm_num :
    (9354674/1000000000:ℝ) ≤ 131/10000) (Real.rpow_nonneg positiveX.le _))

#print axioms pi_300
#print axioms psi_300
#print axioms psi_01310_current_inputs
end SynergyAnalytic.HeightPoint.PureKernelPiPsi300
