/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveQueries
namespace RamanujanPV.PackedSieveCounts
open PackedSieveKernel PackedSieveByteCount QuotientCCell
set_option autoImplicit false
set_option maxHeartbeats 0

theorem p_population : byteCount 125000 (primeBits 38358837684 1000000)=40916 := by
  have result := PackedSieveQueries.p_value 284 (by decide)
  change lowCount 1000000 (primeBits 38358837684 1000000)=40916 at result
  have width := PackedSieveByteWidth.byteCount_ceil_width 38358837684 1000000
  rw [show (1000000+7)/8=125000 by decide] at width
  exact width.trans result

theorem p_source : SourceExecution 38359837683 1644714148 := by
  have result := (PackedSieveQueries.row_source_counts 284 (by decide)).1
  change SourceExecution 38359837683 1644714148 at result
  exact result

theorem p_primeCounting : Nat.primeCounting 38359837683=1644714148 :=
  source_execution_count p_source

#print axioms p_population
#print axioms p_source
#print axioms p_primeCounting
end RamanujanPV.PackedSieveCounts
