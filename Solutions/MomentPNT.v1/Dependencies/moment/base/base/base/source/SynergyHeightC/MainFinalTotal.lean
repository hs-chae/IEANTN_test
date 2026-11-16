/- The actual final memory value, source emission argument and ANT input coincide.
The whole source-main return and final flush association are separate obligations. -/
import SynergyHeightC.MainBudgetSourceSum
import SynergyHeightC.MainTotalOutput
import SourceMainWeightsV1.PNT
namespace SynergyHeightC.MainFinalTotal
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
open Real IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

theorem exact_source_total : SourceMainBudgetV1.Data.total 768=SourceMainWeightsV1.All.total :=
  Option.some.inj ((MainBudgetSourceSum.prefix_value 768 (by decide)).symm.trans
    SourceMainWeightsV1.All.exact_total)

theorem source_total_representable :
    SynergyC.SourceIntervalMath.representable (SourceMainBudgetV1.Data.total 768) := by
  rw [exact_source_total]
  unfold SynergyC.SourceIntervalMath.representable SynergyC.Word512.Range
  decide +kernel

theorem source_total_word_bound : realWord (SourceMainBudgetV1.Data.total 768).hi ≤
    8433850764/1000000000000 := by
  rw [exact_source_total]
  exact SourceMainWeightsV1.PNT.actual_word_bound

theorem actual_read_identity {box : ProofBox}
    (read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
      (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented box,
        FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768)) :
    box=SourceMainBudgetV1.Data.total 768 := by
  have pair := Option.some.inj (read.symm.trans
    (MainTotalOutput.read_total FullMainPrefix.service (SourceMainBudgetV1.Data.total 768) 768))
  exact MainTotalOutput.represented_injective (congrArg Prod.fst pair)

/-- The source provider uses each actual running prefix total, not a separate
zero-total family. The boxes and pointers are the same main-frame outputs. -/
theorem actual_running_source_family : PointExecuteAPI.SourcePointOutputFamily :=
  fun i hi=>SourceMainFramesV1.All.outputs (SourceMainBudgetV1.Data.total i) i hi

/-- The mathematical sum is identified with the value read from actual final
C memory. Thus this consumer uses its source-produced output argument. -/
theorem pi_from_actual_total_read {box : ProofBox}
    (read : evalExpr SynergyC.Header.layout FullMainPrefix.service 1
      (FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768) (.var "total")=
      some (SynergyC.SourceIntervalMath.represented box,
        FullMainEdges.loopState (SourceMainBudgetV1.Data.total 768) 768))
    (h : PrimaryInputs (3681/10000) (3599/10000))
    (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
    (hsmall : ZeroCount.v1.rvm_error_small)
    (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
    (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
    (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ (8441646/1000000000) 0 (7/8) (Real.exp 330) := by
  have same : box=SourceMainBudgetV1.Data.total 768 := actual_read_identity read
  have sum : prefixSum logCellCount=some box :=
    (MainBudgetSourceSum.prefix_value 768 (by decide)).trans
      (congrArg some same.symm)
  have bound : realWord box.hi ≤ 8433850764/1000000000000 := by
    rw [same]
    exact source_total_word_bound
  exact pi_008441646_from_actual_weights actual_running_source_family
    SourceMainWeightsV1.All.all_domains (out:=box) sum bound
    h hCHJ hrvm hsmall hlow hRH hQRH

#print axioms exact_source_total
#print axioms source_total_representable
#print axioms source_total_word_bound
#print axioms actual_read_identity
#print axioms actual_running_source_family
#print axioms pi_from_actual_total_read
end SynergyHeightC.MainFinalTotal
