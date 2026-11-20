/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.SegmentCFunction
import RamanujanPV.QuotientCountRealization

/-! A positive actual segmented-checker execution supplies every intermediate
prime count, not merely the final count. This is the interface required by the
existing source-count/cell consumers. No numeric result is trusted by naming a
successful native process or by postulating correct input classifications. -/
namespace RamanujanPV.SegmentNetwork
open QuotientCMachine SegmentMemory SegmentCheckerMath SegmentCFunctionPrefix
open QuotientCCell
set_option autoImplicit false

theorem classification_count_at {lo hi i : Nat} {claims : Nat→Nat}
    (hlo : 2≤lo) (hindex : i<hi-lo+1)
    (classifications : ∀j,j<hi-lo+1→claims j=if Nat.Prime (lo+j) then 1 else 0) :
    Nat.primeCounting (lo+i)=Nat.primeCounting (lo-1)+
      (∑j∈Finset.range (i+1),claims j) := by
  have count := SegmentCounts.count_increment (lo:=lo) (hi:=lo+i) hlo (by omega)
  have length : lo+i-lo+1=i+1 := by omega
  rw [length] at count
  rw [count]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have index := Finset.mem_range.mp hj
  rw [classifications j (by omega),final_flag hlo (by omega)]

/-- Every offset count derived from the actual segmented checker's accepted
source execution becomes an execution of the existing verified count source.
This directly supplies the source-count objects consumed by IEANTN's cells. -/
theorem source_count_at {call : Service} {s t : State}
    {lo hi capacity cb fb output baseValue i : Nat} {claims : Nat→Nat} {raw : Value}
    (hlo : 2≤lo) (horder : lo≤hi) (hhi : hi≤2000000000000)
    (hcapacity : hi-lo+1≤capacity) (disjoint : cb≠fb)
    (owned : Owned s.heap) (buffer : SegmentCInit.Buffer s.heap fb (hi-lo+1))
    (claimRep : FlagsRep s.heap cb (hi-lo+1) claims)
    (env : Inputs lo hi capacity cb fb s.env)
    (run : Run call SegmentCheckerSource.checkerFunction.body s (.returned t raw))
    (converted : uint64 raw=some (.u64 output)) (positive : 0<output)
    (base : SourceExecution (lo-1) baseValue) (index : i<hi-lo+1) :
    SourceExecution (lo+i) (baseValue+∑j∈Finset.range (i+1),claims j) := by
  obtain ⟨outputValue,classifications,increment⟩ := SegmentCFunction.positive_output_sound
    hlo horder hhi hcapacity disjoint owned buffer claimRep env run converted positive
  apply QuotientCountRealization.source_execution_from_kernel_value (by omega) (by omega)
  rw [classification_count_at hlo index classifications,source_execution_count base]

#print axioms classification_count_at
#print axioms source_count_at
end RamanujanPV.SegmentNetwork
