/- Actual observed final128bytes from the pinned unchanged C main.
These are observations compared to the independently source-proved computation,
never replacement numerical providers or new mathematical premises. -/
import SynergyHeightC.MainCompleteModel
namespace SynergyHeightC.MainObservedOutput
open ScopedC ScopedC.Machine ScopedNumerical SynergyBasis ScopedIO
open SynergyAnalytic SynergyAnalytic.HeightPoint SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option maxRecDepth 100000

def total : ProofBox := ⟨2869890699926766771202866067252394067,2869890699926766771254572444732902052⟩
def bytes : List Nat := [83,56,123,158,12,192,216,181,7,169,245,52,137,184,40,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,164,74,212,196,185,114,144,182,7,169,245,52,137,184,40,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

theorem total_exact : SourceMainBudgetV1.Data.total 768=total :=
  MainFinalTotal.exact_source_total

theorem bytes_exact : bytes=EmitUBuffer.bytes total.lo++EmitUBuffer.bytes total.hi := by
  decide +kernel

theorem actual_source_bytes : bytes=EmitUBuffer.bytes (SourceMainBudgetV1.Data.total 768).lo++
    EmitUBuffer.bytes (SourceMainBudgetV1.Data.total 768).hi :=
  bytes_exact.trans (congrArg
    (fun b : ProofBox=>EmitUBuffer.bytes b.lo++EmitUBuffer.bytes b.hi) total_exact.symm)

theorem actual_source_sum : prefixSum logCellCount=some total :=
  (MainBudgetSourceSum.prefix_value 768 (by decide)).trans (congrArg some total_exact)

theorem observed_upper_word_bound : realWord total.hi ≤ 8433850764/1000000000000 := by
  rw [←total_exact]
  exact MainFinalTotal.source_total_word_bound

#print axioms total_exact
#print axioms bytes_exact
#print axioms actual_source_bytes
#print axioms actual_source_sum
#print axioms observed_upper_word_bound
end SynergyHeightC.MainObservedOutput
