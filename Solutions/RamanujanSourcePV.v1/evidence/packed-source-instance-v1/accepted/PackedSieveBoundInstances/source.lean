/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveInstances

/-! Explicit result bundles associate both actual C source payloads with the
same ASTs used by the proved segment and counter executions. Native loading,
process execution and stdout association are separate documented boundaries. -/
namespace RamanujanPV.PackedSieveBoundInstances
open QuotientCCell

def SourceBindings : Prop :=
  LCMSourcePV.RestrictedC.SourceCorresponds SegmentCheckerSource.render
    SegmentCheckerSource.actualSource SegmentCheckerSource.functions ∧
  LCMSourcePV.RestrictedC.SourceCorresponds QuotientCSourceV2.render
    QuotientCSourceV2.actualSource ()

theorem source_bindings : SourceBindings :=
  ⟨SegmentCheckerSource.actual_source_checked, QuotientCSourceV2.actual_source_checked⟩

theorem source_bound_1000 : SourceBindings ∧
    SourceExecution 38358838683 1644673264 ∧
    Nat.primeCounting 38358838683 = 1644673264 :=
  ⟨source_bindings, PackedSieveInstances.source_1000, PackedSieveInstances.pi_1000⟩

theorem source_bound_65536 : SourceBindings ∧
    SourceExecution 38358903219 1644675896 ∧
    Nat.primeCounting 38358903219 = 1644675896 :=
  ⟨source_bindings, PackedSieveInstances.source_65536, PackedSieveInstances.pi_65536⟩

#print axioms source_bindings
#print axioms source_bound_1000
#print axioms source_bound_65536
end RamanujanPV.PackedSieveBoundInstances
