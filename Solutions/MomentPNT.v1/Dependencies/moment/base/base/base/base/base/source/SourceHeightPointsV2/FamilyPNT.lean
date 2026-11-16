/- Semantic source-output consumer independent of the evaluator. The original source-execution
   instances, main input construction and I/O are explicit unfinished work. -/
import SourceHeightPointsV2.OutputFamily
import SynergyAnalytic.HeightPNTInstance
import SynergyAnalytic.PrimeRichWidth
namespace SynergyHeightC.PointExecuteAPI
open ScopedC SynergyAnalytic SynergyAnalytic.HeightPoint
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The source-checked C output intervals supply the actual whole-cell
zero-count caps. This replaces the model-only endpoint provider in the selected
PNT path, conditional on closing all original 768 C executions. -/
theorem actual_height_caps_of_output_family (points : SourcePointOutputFamily)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height) :
    ActualHeightCaps heightEndpoint cValue DValue logCellCount := by
  have hc := endpoint_any_width_actual_height_caps heightEndpoint_monotone
    heightEndpoint_zero heightEndpoint_last h
    (family_endpoint_caps points kernel_generic_height_all) hRH
  have hC : (fun i => baseC i+21600) = cValue := funext (fun i => (cValue_eq i).symm)
  have hD : baseD = DValue := funext (fun i => (DValue_eq i).symm)
  rw [hC,hD] at hc
  exact hc

/-- Exact original fourteen analytic premises and the tighter completed
mathematical conclusion; remaining numerical source obligations are the finite
SourcePointOutputsProvider parameter. This conditional theorem is not a completed
application source-first PV claim. -/
theorem pi_008441646_of_output_family (points : SourcePointOutputFamily)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) := by
  have hb := source_pi_from_count_cells heightEndpoint_monotone heightEndpoint_zero
    heightEndpoint_last h (actual_height_caps_of_output_family points h hRH)
    hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have hh := hb x hx
  have hx0 : 0 < x := (Real.exp_pos 330).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right final_height_budget_tight (by positivity))

theorem pi_008442_of_output_family (points : SourcePointOutputFamily)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (4221/500000) 0 (7/8) (Real.exp 330) := by
  have hb := pi_008441646_of_output_family points h hCHJ hrvm hsmall hlow hRH hQRH
  intro x hx
  have hh := hb x hx
  have hx0 : 0 < x := (Real.exp_pos 330).trans_le hx
  simp only [pow_zero,mul_one] at hh ⊢
  exact hh.trans (mul_le_mul_of_nonneg_right (by norm_num :
    (8441646/1000000000:ℝ) ≤ 4221/500000) (by positivity))

theorem prime_rich_017_of_output_family (points : SourcePointOutputFamily)
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8))
    {x : ℝ} (hx : Real.exp 330 ≤ x) :
    (57/500000:ℝ)*x^((7:ℝ)/8)/Real.log x ≤
      primeCounting (x+(17/1000:ℝ)*x^((7:ℝ)/8))-primeCounting x :=
  prime_rich_017_008442 (pi_008442_of_output_family points h hCHJ hrvm hsmall hlow hRH hQRH) hx

#print axioms actual_height_caps_of_output_family
#print axioms pi_008441646_of_output_family
#print axioms pi_008442_of_output_family
#print axioms prime_rich_017_of_output_family
end SynergyHeightC.PointExecuteAPI
