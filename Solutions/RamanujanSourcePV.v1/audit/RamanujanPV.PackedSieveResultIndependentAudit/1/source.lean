/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveResult
import Lean.Util.FoldConsts
/-! Independent complete joint-wrapper closure audit. Prior three-root audit
is preserved. No numerical re-evaluation, physical loading or new source model. -/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  let required : List Name := [
    `RamanujanPV.PackedSieveResult.actual_source_bindings,
    `RamanujanPV.QuotientCSourceV2.actual_source_checked,
    `RamanujanPV.QuotientDriverSource.actual_source_checked,
    `RamanujanPV.SegmentCheckerSource.actual_source_checked,
    `RamanujanPV.FiniteExpSource.actual_source_checked,
    `RamanujanPV.FiniteLogSource.actual_source_checked,
    `RamanujanPV.FiniteCellSource.actual_source_checked,
    `RamanujanPV.PackedSieveQueries.row_source_counts,
    `RamanujanPV.PackedSieveProvider.source_bound_provider,
    `RamanujanPV.SegmentCFunction.positive_output_sound,
    `RamanujanPV.QuotientCFunction.linked_function_refines,
    `RamanujanPV.PackedSievePrimitiveMaskMillion.packed_bits,
    `RamanujanPV.PackedSievePrimitiveQWindow.packed_bits,
    `RamanujanPV.FiniteCellProtected.positive_implies_strict,
    `IEANTN.primeCounting]
  let forbidden := ["RamanujanPV.LocalPrimeTree.","RamanujanPV.LocalLucas.",
    "RamanujanPV.LocalWindowMillion.","RamanujanPV.LocalCells1000.",
    "RamanujanPV.CriticalSourceClosed.","RamanujanPV.SegmentSourceMargins.",
    "RamanujanPV.SegmentRamanujanMillion.","RamanujanPV.FiniteProgramMillion.",
    "RamanujanPV.FiniteGuardedMillion.","RamanujanPV.FiniteGuardedResult.",
    "RamanujanPV.HighTransitionCount."]
  let forbiddenExact : List Name := [
    `RamanujanPV.PrimeWindow.count_at,`RamanujanPV.PrimeWindow.source_count_at,
    `RamanujanPV.WindowCells.row_counts,`RamanujanPV.WindowCells.row_real_enclosures,
    `RamanujanPV.WindowCells.checkRow_clauses,`RamanujanPV.LocalCellsMillion.checked,
    `RamanujanPV.SegmentWindowCells.complete_certificate,
    `RamanujanPV.PackedSieveKernel.swarCount,`RamanujanPV.PackedSieveKernel.scoutCount]
  for root in [`RamanujanPV.PackedSieveResult.source_linked_uniform_gap,
      `RamanujanPV.PackedSieveResult.source_linked_real_interval] do
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut parents : Std.HashMap Name Name := {}
    let mut pending := [root]
    let mut axioms : NameSet := {}
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      let some info := env.find? name | throwError "Missing wrapper dependency {name}"
      if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
        throwError "Admitted/native execution leaf {name}"
      for pre in forbidden do
        if name.toString.startsWith pre then throwError "Forbidden old proof path {name}"
      if forbiddenExact.contains name then throwError "Forbidden old provider {name}"
      match info with
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Nonstandard joint-wrapper axiom {name}"
        axioms := axioms.insert name
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if !seen.contains dependency then
          seen := seen.insert dependency
          parents := parents.insert dependency name
          pending := dependency :: pending
    let expectedMath := if root == `RamanujanPV.PackedSieveResult.source_linked_uniform_gap then
      `RamanujanPV.PackedSieveMillion.uniform_gap else
      `RamanujanPV.PackedSieveMillion.first_1000001_real_interval
    for name in expectedMath :: required do
      unless seen.contains name do throwError "Missing actual joint binding/count/math path {name}"
      let mut path := [name]
      let mut next := name
      while next != root do
        let some previous := parents[next]? | throwError "Broken actual wrapper path {next}"
        path := previous :: path
        next := previous
      logInfo m!"PACKED_JOINT_ACTUAL_PATH {root}: {String.intercalate " -> " (path.map toString)}"
    unless !(env.find? root).get!.type.isForall do
      throwError "Unexpected external assumption on joint source result {root}"
    logInfo m!"PACKED_JOINT_COMPLETE_CLOSURE {root} {seen.size}"
    logInfo m!"PACKED_JOINT_COMPLETE_AXIOMS {root} {axioms.toList}"
namespace RamanujanPV.PackedSieveResultIndependentAudit
set_option autoImplicit false
example : PackedSieveResult.SourceBindings ∧
    ∀x : ℝ,(38358837683:ℝ)≤x→x<38359837684→(501901:ℝ)<gap x :=
  PackedSieveResult.source_linked_uniform_gap
example : PackedSieveResult.SourceBindings ∧
    ∀x : ℝ,(38358837683:ℝ)≤x→x<38359837684→Holds x :=
  PackedSieveResult.source_linked_real_interval
#print axioms PackedSieveResult.source_linked_uniform_gap
#print axioms PackedSieveResult.source_linked_real_interval
end RamanujanPV.PackedSieveResultIndependentAudit
