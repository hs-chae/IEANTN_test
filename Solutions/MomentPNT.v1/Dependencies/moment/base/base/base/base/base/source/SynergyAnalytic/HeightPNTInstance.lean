import SynergyAnalytic.HeightGenericAll
import SynergyAnalytic.HeightFiniteBudget
import SynergyAnalytic.HeightTightBudget
import SynergyAnalytic.EndpointAnyWidth
namespace SynergyAnalytic.HeightPoint
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_height_cells
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height) :
    ActualHeightCaps heightEndpoint cValue DValue logCellCount := by
  have hc:=endpoint_any_width_actual_height_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last h
    (endpoint_caps_of_all_checks kernel_generic_height_all) hRH
  have hC : (fun i=>baseC i+21600)=cValue := funext (fun i=>(cValue_eq i).symm)
  have hD : baseD=DValue := funext (fun i=>(DValue_eq i).symm)
  rw [hC,hD] at hc
  exact hc

/-- Complete mathematical PNT consumer for the fixed768-cell logarithmic mesh.
The new point enclosures,768 D-domain facts,24 finite-budget blocks and272-cell
J-basis caps are all discharged by ordinary kernel proofs. This is not by itself
source-first C PV. The historical old-bank version inherits six native scalar
leaves; the separate kernel-overlay build removes those leaves. Actual C
execution/source/I/O association remains a separate source-first obligation. -/
theorem source_pi_008442
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (4221/500000) 0 (7/8) (Real.exp 330) := by
  have hb:=source_pi_from_count_cells heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last h
    (actual_height_cells h hRH) hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have hh:=hb x hx
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right final_height_budget (by positivity))


/-- Tighter rounding of exactly the same verified768-point/24-block computation. -/
theorem source_pi_008441646
    (h:PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ:OriginalCHJSource) (hrvm:ZeroCount.v1.rvm_error_bound)
    (hsmall:ZeroCount.v1.rvm_error_small) (hlow:LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH:RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH:ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) := by
  have hb:=source_pi_from_count_cells heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last h
    (actual_height_cells h hRH) hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have hh:=hb x hx
  have hx0 : 0<x := (Real.exp_pos 330).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right final_height_budget_tight (by positivity))

#print axioms actual_height_cells
#print axioms source_pi_008442
#print axioms source_pi_008441646
end SynergyAnalytic.HeightPoint
