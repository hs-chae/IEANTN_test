/- Both earlier-onset error bounds consume the actual source-main physical total.
The directψsource bridge is independent ofπ and preserves all fourteen analytic inputs. -/
import SynergyHeightC.MainRationalClosed
import SynergyAnalytic.HeightPiPsi300
namespace SynergyHeightC.MainPiPsi300Read
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

theorem pi_psi_300_from_actual_total_read
    {out : ProofBox}
    (read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
      (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented out,
        FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768))
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (9354674/1000000000) 0 (7/8) (Real.exp 300) ∧
      HasPowerLogBound Eψ (9354674/1000000000) 0 (7/8) (Real.exp 300) := by
  have finite := MainRationalRead.finite_from_actual_total_read read
  have caps := source_actual_height_caps MainFinalTotal.actual_running_source_family
    SourceMainWeightsV1.All.all_domains h hRH
  have slopes : ∀ i < logCellCount, 0 ≤ pointD i ∧ pointD i ≤ 163 :=
    fun i hi=>⟨(by norm_num : (0:ℝ)≤77).trans (SourcePointSlopesV1.All.bounds i hi).1,
      (SourcePointSlopesV1.All.bounds i hi).2⟩
  exact ⟨pi_300_of_height_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
      MainRationalProfile.source_weights_nonnegative slopes finite h caps
      hCHJ hrvm hsmall hlow hRH hQRH,
    psi_300_of_height_caps heightEndpoint_monotone heightEndpoint_zero heightEndpoint_last
      MainRationalProfile.source_weights_nonnegative slopes finite h caps
      hCHJ hrvm hsmall hlow hRH hQRH⟩

#print axioms pi_psi_300_from_actual_total_read
end SynergyHeightC.MainPiPsi300Read
