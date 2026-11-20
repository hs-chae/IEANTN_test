/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveProvider
import RamanujanPV.PackedSieveSlices
import RamanujanPV.PackedSievePrimitiveBits
import Lean.Util.FoldConsts

/-! Bounded independent inspection of generic packed certificates and the
source-bound segmented checker. This does not assert a ground numerical count
or verification of a physical packed generator/loader. The exact source-count
anchor remains an explicit application premise. Frozen source files are unchanged. -/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let provider : List Name := [
    `RamanujanPV.SegmentCheckerSource.actual_source_checked,
    `RamanujanPV.SegmentCheckerSource.checkerFunction,
    `RamanujanPV.PackedSieveProvider.source_provider,
    `RamanujanPV.PackedSieveProvider.input_owned,
    `RamanujanPV.PackedSieveProvider.input_scratch,
    `RamanujanPV.PackedSieveProvider.input_claims,
    `RamanujanPV.QuotientDriverInit.source_static_initialization,
    `RamanujanPV.QuotientDriverInit.initialized_owned,
    `RamanujanPV.QuotientDriverInit.canonicalLayout,
    `RamanujanPV.SegmentCFunctionPrefix.input_env,
    `RamanujanPV.PackedSieveSource.source_execution,
    `RamanujanPV.PackedSieveSource.classified_claims,
    `RamanujanPV.PackedSieveCorrect.primeBits_prime,
    `RamanujanPV.PackedSieveCorrect.compositeMask_iff,
    `RamanujanPV.PackedSieveCorrect.base_unmarked_prime,
    `RamanujanPV.PackedSieveMaskRefinement.divisorMask_sound_complete,
    `RamanujanPV.PackedSieveGeometric.testBit_geomMask,
    `RamanujanPV.PackedSieveByteCount.table_correct,
    `RamanujanPV.PackedSieveByteCount.byteCount_correct,
    `RamanujanPV.PackedSieveByteWidth.primeBits_support,
    `RamanujanPV.PackedSievePrefix.byteCount_prefix,
    `RamanujanPV.SegmentCFunction.correct_claims_execution,
    `RamanujanPV.SegmentCFunction.incorrect_claims_execution,
    `RamanujanPV.SegmentCFunction.positive_output_sound,
    `RamanujanPV.SegmentCFunctionPrefix.prefix_exec,
    `RamanujanPV.SegmentCInit.initialization_loop,
    `RamanujanPV.SegmentCDivisors.divisor_for_exec,
    `RamanujanPV.SegmentCClaims.matching_loop,
    `RamanujanPV.QuotientCDeterminism.returned_unique,
    `RamanujanPV.SegmentNetwork.source_count_at,
    `RamanujanPV.QuotientCountRealization.source_execution_from_kernel_value,
    `RamanujanPV.QuotientCFunction.linked_function_refines,
    `RamanujanPV.QuotientCCell.SourceExecution]
  let forbidden := ["RamanujanPV.PackedSieveSealedMillion.",
    "RamanujanPV.PackedSieveSealedQWindow.","RamanujanPV.PackedSieveInstances.",
    "RamanujanPV.PackedSieveQueries.","RamanujanPV.HighTransitionCount.",
    "RamanujanPV.LocalWindowMillion."]
  for (root,required) in [
      (`RamanujanPV.PackedSieveProvider.source_bound_provider,provider),
      (`RamanujanPV.PackedSieveByteTail.byteCountFast_ceil_width,
        [`RamanujanPV.PackedSieveByteCount.table_correct,
         `RamanujanPV.PackedSieveByteTail.byteCountFast_eq,
         `RamanujanPV.PackedSieveByteWidth.byteCount_ceil_width]),
      (`RamanujanPV.PackedSieveSlices.checkSlices_from_zero,
        [`RamanujanPV.PackedSieveSlices.checkSlices_sound,
         `RamanujanPV.PackedSieveSlices.prefix_difference,
         `RamanujanPV.PackedSieveByteTail.byteCountFast_eq,
         `RamanujanPV.PackedSieveByteCount.table_correct])] do
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut parents : Std.HashMap Name Name := {}
    let mut pending := [root]
    let mut axioms : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      let some info := env.find? name | throwError "Missing inspected packed constant: {name}"
      for oldNamespace in forbidden do
        if name.toString.startsWith oldNamespace then
          throwError "Ground numerical result unexpectedly required by generic theorem: {name}"
      if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
        throwError "Admitted/native leaf in generic packed path: {name}"
      if name == `RamanujanPV.PackedSieveKernel.swarCount ||
          name == `RamanujanPV.PackedSieveKernel.scoutCount then
        throwError "Unproved SWAR scout used in accepted byte provider: {name}"
      match info with
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Nonstandard packed-source axiom: {name}"
        axioms := axioms.insert name
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if !seen.contains dependency then
          seen := seen.insert dependency
          parents := parents.insert dependency name
          pending := dependency::pending
    for name in required do
      unless seen.contains name do
        throwError "Missing required actual packed/source path in {root}: {name}"
      let mut path := [name]
      let mut next := name
      while next != root do
        let some previous := parents[next]? | throwError "Broken packed dependency path"
        path := previous::path
        next := previous
      logInfo m!"PACKED_CHECKED_PATH {root}: {String.intercalate " -> " (path.map toString)}"
    logInfo m!"PACKED_COMPLETE_CONSTANT_CLOSURE {root} {seen.size}"
    logInfo m!"PACKED_COMPLETE_AXIOM_UNIVERSE {root} {axioms.toList}"

namespace RamanujanPV.PackedSieveProviderIndependentAudit
open QuotientCCell PackedSieveProvider PackedSieveKernel PackedSieveByteCount PackedSievePrefix
set_option autoImplicit false

/-- The precise generic type retains only a proved source-count anchor plus
range/capacity conditions. No heap/flags/classification/expected-output premise. -/
example {lo count baseValue : Nat}
    (base : SourceExecution (lo-1) baseValue)
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (storage : count ≤ QuotientDriverSource.capacity) :
    LCMSourcePV.RestrictedC.SourceCorresponds SegmentCheckerSource.render
      SegmentCheckerSource.actualSource SegmentCheckerSource.functions ∧
    CountProvider lo count baseValue :=
  PackedSieveProvider.source_bound_provider base hlo hcount upper storage

/-- The resulting object certifies the actual Nat prime count at every
in-range prefix; the anchor is consumed through its source execution proof. -/
example {lo count baseValue i : Nat}
    (base : SourceExecution (lo-1) baseValue)
    (hlo : 2 ≤ lo) (hcount : 0 < count) (upper : lo+count-1 ≤ 2000000000000)
    (storage : count ≤ QuotientDriverSource.capacity) (index : i < count) :
    Nat.primeCounting (lo+i) = baseValue+
      byteCount ((i+8)/8) (prefixBits (i+1) (primeBits lo count)) :=
  source_execution_count (source_provider base hlo hcount upper storage i index)

/-- The existing quotient source byte binding is checked separately: the
provider's explicit conjunct binds the segmented checker C source. -/
example : LCMSourcePV.RestrictedC.SourceCorresponds QuotientCSourceV2.render
    QuotientCSourceV2.actualSource () := QuotientCSourceV2.actual_source_checked

example (lo count : Nat) :
    PackedSievePrimitiveBits.primitiveBits lo count = primeBits lo count :=
  PackedSievePrimitiveBits.primitiveBits_eq lo count

#print axioms PackedSievePrimitiveBits.primitiveBits_eq
#print axioms PackedSieveProvider.source_bound_provider
#print axioms PackedSieveByteTail.byteCountFast_ceil_width
#print axioms PackedSieveSlices.checkSlices_from_zero
#print axioms QuotientCSourceV2.actual_source_checked
end RamanujanPV.PackedSieveProviderIndependentAudit
