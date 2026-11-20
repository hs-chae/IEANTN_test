/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.DemandCriticalPair.Final
import RamanujanPV.QuotientCountRealization

/-! The identical previously verified count anchors, without importing unrelated
local prime certificates or prior finite-interval consumers. No new input count
or source-execution assumption is introduced. -/
namespace RamanujanPV.PackedSieveAnchors
open QuotientCCell
set_option autoImplicit false

theorem p_source : SourceExecution 38358837683 1644673232 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num)
    DemandCriticalPair.pi_38358837683

theorem q_source : SourceExecution 14111427770 632207037 :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num)
    DemandCriticalPair.pi_14111427770

#print axioms p_source
#print axioms q_source
end RamanujanPV.PackedSieveAnchors
