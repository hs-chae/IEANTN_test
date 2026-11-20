/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveMillion
import Lean.Util.FoldConsts

/-! Independent complete proof/type closure and actual compiled import census.
The two real consumers share the closed certificate: its entire inspected closure
is reused only after confirming that the consumer actually refers to that exact
certificate constant. No source-selection heuristic substitutes for imports.
Original raw row/data imports remain unchanged; old proof providers are rejected.
This inspection adds no axiom and verifies no physical loader/native generator. -/
open Lean Elab Command
set_option maxHeartbeats 0
run_cmd do
  let env ← getEnv
  for name in env.header.moduleNames do
    logInfo m!"PACKED_ACTUAL_IMPORTED_MODULE {name}"
  logInfo m!"PACKED_ACTUAL_IMPORTED_MODULE_COUNT {env.header.moduleNames.size}"
  let common : List Name := [
    `RamanujanPV.PackedSieveMillion.layout_checked,
    `RamanujanPV.PackedSieveFiniteCells.complete_certificate,
    `RamanujanPV.PackedSieveQueries.row_source_counts,
    `RamanujanPV.PackedSieveQueries.p_value,
    `RamanujanPV.PackedSieveQueries.q_value,
    `RamanujanPV.PackedSieveQueries.p_slices_checked,
    `RamanujanPV.PackedSieveQQueries.checked,
    `RamanujanPV.PackedSievePrimitiveMaskMillion.primitive_bits,
    `RamanujanPV.PackedSievePrimitiveMaskMillion.packed_bits,
    `RamanujanPV.PackedSievePrimitiveQWindow.primitive_bits,
    `RamanujanPV.PackedSievePrimitiveQWindow.packed_bits,
    `RamanujanPV.PackedSievePrimitiveBits.primitiveBits_eq,
    `RamanujanPV.PackedSieveSlices.checkSlices_from_zero,
    `RamanujanPV.PackedSieveSlices.prefix_difference,
    `RamanujanPV.PackedSieveProvider.source_bound_provider,
    `RamanujanPV.PackedSieveProvider.source_provider,
    `RamanujanPV.PackedSieveProvider.input_owned,
    `RamanujanPV.PackedSieveProvider.input_scratch,
    `RamanujanPV.PackedSieveProvider.input_claims,
    `RamanujanPV.PackedSieveByteCount.table_correct,
    `RamanujanPV.PackedSieveByteCount.byteCount_correct,
    `RamanujanPV.PackedSieveAnchors.p_source,
    `RamanujanPV.PackedSieveAnchors.q_source,
    `RamanujanPV.DemandCriticalPair.pi_38358837683,
    `RamanujanPV.DemandCriticalPair.pi_14111427770,
    `RamanujanPV.SegmentCheckerSource.actual_source_checked,
    `RamanujanPV.SegmentCFunction.correct_claims_execution,
    `RamanujanPV.SegmentCFunction.positive_output_sound,
    `RamanujanPV.SegmentNetwork.source_count_at,
    `RamanujanPV.QuotientCountRealization.source_execution_from_kernel_value,
    `RamanujanPV.QuotientCFunction.linked_function_refines,
    `RamanujanPV.FiniteCellProtected.positive_implies_strict,
    `RamanujanPV.FiniteCellProtected.reference_run,
    `RamanujanPV.FiniteCellSource.actual_source_checked,
    `RamanujanPV.FiniteCellExecution.service_closed,
    `RamanujanPV.FiniteScalarEval.returned_value_sound,
    `RamanujanPV.FiniteLogExecution.source_log_upper_sound,
    `RamanujanPV.FiniteLogExecution.service_closed,
    `RamanujanPV.FiniteLogServices.ceil_service_closed,
    `RamanujanPV.FiniteLogSource.actual_source_checked,
    `RamanujanPV.FiniteWideExpEnclosures.source_e_scaled,
    `RamanujanPV.FiniteWideExpLinked.service_closed,
    `RamanujanPV.FiniteWideExpExecute.low_source_run,
    `RamanujanPV.FiniteExpSource.actual_source_checked,
    `RamanujanPV.FiniteScalarMillion.all_cell_domains,
    `RamanujanPV.FiniteScalarMillion.all_cell_source,
    `RamanujanPV.FiniteScalarMillion.all_log_source]
  let forbiddenNames : List Name := [
    `RamanujanPV.PrimeWindow.count_at,
    `RamanujanPV.PrimeWindow.source_count_at,
    `RamanujanPV.WindowCells.row_counts,
    `RamanujanPV.WindowCells.row_real_enclosures,
    `RamanujanPV.WindowCells.checkRow_clauses,
    `RamanujanPV.WindowCells.complete_certificate,
    `RamanujanPV.LocalCellsMillion.checked,
    `RamanujanPV.LocalCellsMillion.conditional_certificate,
    `RamanujanPV.LocalCellsMillion.conditional_holds,
    `RamanujanPV.SegmentWindowCells.complete_certificate,
    `RamanujanPV.PackedSieveKernel.swarCount,
    `RamanujanPV.PackedSieveKernel.scoutCount]
  let forbiddenPrefixes := ["RamanujanPV.LocalPrimeTree.","RamanujanPV.LocalLucas.",
    "RamanujanPV.LocalWindowMillion.","RamanujanPV.LocalCells1000.",
    "RamanujanPV.CriticalSourceClosed.","RamanujanPV.SegmentSourceMargins.",
    "RamanujanPV.SegmentRamanujanMillion.","RamanujanPV.FiniteProgramMillion.",
    "RamanujanPV.FiniteGuardedMillion.","RamanujanPV.FiniteSourceCells.",
    "RamanujanPV.HighTransitionCount."]
  for name in forbiddenNames do logInfo m!"PACKED_FORBIDDEN_EXACT {name}"
  for pre in forbiddenPrefixes do logInfo m!"PACKED_FORBIDDEN_PREFIX {pre}"
  let base := `RamanujanPV.PackedSieveMillion.complete_certificate
  let mut baseSeen : NameSet := {}
  let mut baseParents : Std.HashMap Name Name := {}
  let mut baseAxioms : NameSet := {}
  for (root,extra) in [(base,([] : List Name)),
      (`RamanujanPV.PackedSieveMillion.first_1000001_real_interval,
        [`IEANTN.primeCounting,`RamanujanPV.complete_certificate_sound,
         `RamanujanPV.fixed_cell_sound]),
      (`RamanujanPV.PackedSieveMillion.uniform_gap,
        [`IEANTN.primeCounting,`RamanujanPV.CertificateMargin.array_certificate,
         `RamanujanPV.PackedSieveMillion.margins_checked,
         `RamanujanPV.WindowMargin.check,`RamanujanPV.FinitePredicateBounds.floor_relation])] do
    let mut seen := baseSeen.insert root
    let mut parents := baseParents
    let mut axioms := baseAxioms
    let mut pending := [root]
    let mut encounteredBase := root == base
    while !pending.isEmpty do
      let name := pending.head!
      pending := pending.tail!
      let some info := env.find? name | throwError "Missing actual inspected constant {name}"
      if forbiddenNames.contains name then throwError "Forbidden old numerical provider {name}"
      for pre in forbiddenPrefixes do
        if name.toString.startsWith pre then throwError "Forbidden proof-provider namespace {name}"
      if name == `sorryAx || name.toString.startsWith "Lean.ofReduceBool" then
        throwError "Admitted/native execution leaf {name}"
      match info with
      | .axiomInfo _ =>
        unless name == `propext || name == `Classical.choice || name == `Quot.sound do
          throwError "Nonstandard axiom {name}"
        axioms := axioms.insert name
      | _ => pure ()
      for dependency in info.getUsedConstantsAsSet.toList do
        if dependency == base && root != base then
          encounteredBase := true
          if !(parents.contains base) then parents := parents.insert base name
        if !seen.contains dependency then
          seen := seen.insert dependency
          parents := parents.insert dependency name
          pending := dependency :: pending
    unless encounteredBase do throwError "Shared certificate not actually consumed by {root}"
    for name in common ++ extra do
      unless seen.contains name do throwError "Missing required current source path in {root}: {name}"
      let mut path := [name]
      let mut next := name
      while next != root do
        let some previous := parents[next]? | throwError "Broken actual dependency path {next}"
        path := previous :: path
        next := previous
      logInfo m!"PACKED_MILLION_CHECKED_PATH {root}: {String.intercalate " -> " (path.map toString)}"
    let mut binders : Nat := 0
    let mut type := (env.find? root).get!.type
    while type.isForall do
      type := type.bindingBody!
      binders := binders + 1
    unless binders == (if root == base then 0 else 3) do
      throwError "Unexpected mathematical/source assumptions in final root {root}: {binders} binders"
    logInfo m!"PACKED_MILLION_BINDER_COUNT {root} {binders}"
    logInfo m!"PACKED_MILLION_COMPLETE_CONSTANT_CLOSURE {root} {seen.size}"
    logInfo m!"PACKED_MILLION_COMPLETE_AXIOM_UNIVERSE {root} {axioms.toList}"
    if root == base then
      baseSeen := seen
      baseParents := parents
      baseAxioms := axioms

namespace RamanujanPV.PackedSieveMillionIndependentAudit
open WindowCells FiniteProgramCells
set_option autoImplicit false
example : CompleteCertificate 38358837683 38359837684
    ((rawList LocalCellsMillion.rows LocalCellsMillion.rowCount).map (fun r => r.toCell eLo eHi)) :=
  PackedSieveMillion.complete_certificate
example {x : ℝ} (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) :
    IEANTN.primeCounting x ^ 2 < Real.exp 1*x/Real.log x*IEANTN.primeCounting (x/Real.exp 1) :=
  PackedSieveMillion.first_1000001_real_interval lower upper
example {x : ℝ} (lower : (38358837683:ℝ)≤x) (upper : x<38359837684) :
    (501901:ℝ)<Real.exp 1*x/Real.log x*IEANTN.primeCounting (x/Real.exp 1)-IEANTN.primeCounting x^2 :=
  PackedSieveMillion.uniform_gap lower upper
#print axioms PackedSieveMillion.complete_certificate
#print axioms PackedSieveMillion.first_1000001_real_interval
#print axioms PackedSieveMillion.uniform_gap
end RamanujanPV.PackedSieveMillionIndependentAudit
