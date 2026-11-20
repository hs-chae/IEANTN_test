/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteGuardedMillion
import Lean.Util.FoldConsts

/-! Inspection of the actual complete proof/type constant closure. This adds
no axiom or mathematical claim; compilation fails if any required source path
is absent or any old numerical/certificate shortcut remains. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let root := ``RamanujanPV.FiniteGuardedMillion.uniform_gap
  let required := [``RamanujanPV.FiniteGuardedMillion.derived_domains,
    ``RamanujanPV.FiniteCellInverse.positive_domain,
    ``RamanujanPV.FiniteCellInverse.log_response_of_guard,
    ``RamanujanPV.QuotientCFunction.function_refines,
    ``RamanujanPV.QuotientCFunction.completed_execution_correct,
    ``RamanujanPV.QuotientCSource.actual_source_checked,
    ``RamanujanPV.FiniteWideExpLinked.service_closed,
    ``RamanujanPV.FiniteWideExpExecute.low_source_run,
    ``RamanujanPV.FiniteLogExecution.service_closed,
    ``RamanujanPV.FiniteLogServices.ceil_service_closed,
    ``RamanujanPV.FiniteProgramCells.complete_certificate,
    ``RamanujanPV.FiniteCellProtected.positive_implies_strict,
    ``RamanujanPV.FiniteCellProtected.reference_run,
    ``RamanujanPV.FiniteCellSource.actual_source_checked,
    ``RamanujanPV.FiniteCellExecution.service_closed,
    ``RamanujanPV.FiniteScalarEval.returned_value_sound,
    ``RamanujanPV.FiniteLogExecution.source_log_upper_sound,
    ``RamanujanPV.FiniteLogSource.actual_source_checked,
    ``RamanujanPV.FiniteWideExpEnclosures.source_e_scaled,
    ``RamanujanPV.FiniteExpSource.actual_source_checked,
    ``RamanujanPV.SegmentCFunction.positive_output_sound,
    ``RamanujanPV.SegmentCFunction.correct_claims_execution,
    ``RamanujanPV.SegmentNetwork.source_count_at,
    ``RamanujanPV.SegmentTableProvider.source_provider]
  let forbidden := [``RamanujanPV.FiniteScalarMillion.all_cell_domains,
    ``RamanujanPV.FiniteProgramMillion.domains,
    ``RamanujanPV.FiniteProgramMillion.complete_certificate,
    ``RamanujanPV.FiniteProgramMillion.source_strict,
    ``RamanujanPV.PrimeWindow.count_at,
    ``RamanujanPV.PrimeWindow.source_count_at,
    ``RamanujanPV.WindowCells.row_counts,
    ``RamanujanPV.WindowCells.row_real_enclosures,
    ``RamanujanPV.WindowCells.checkRow_clauses,
    ``RamanujanPV.WindowCells.complete_certificate,
    ``RamanujanPV.LocalWindowMillion.p_increment,
    ``RamanujanPV.LocalWindowMillion.q_increment,
    ``RamanujanPV.LocalCellsMillion.checked,
    ``RamanujanPV.LocalCellsMillion.conditional_certificate,
    ``RamanujanPV.LocalCellsMillion.conditional_holds,
    ``RamanujanPV.SegmentWindowCells.complete_certificate,
    `RamanujanPV.FiniteSourceCells.complete_certificate,
    ``RamanujanPV.SegmentRamanujanMillion.complete_certificate]
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut parent : Std.HashMap Name Name := {}
  let mut pending := [root]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    let some info := env.find? name | throwError "Missing inspected constant {name}"
    if name.toString.startsWith "RamanujanPV.FiniteScalarMillion.cell_domain_" then
      throwError "Prechecked guard/floor domain numerical provider remains: {name}"
    for dependency in info.getUsedConstantsAsSet.toList do
      if !seen.contains dependency then
        seen := seen.insert dependency
        parent := parent.insert dependency name
        pending := dependency::pending
  for name in required do
    unless seen.contains name do
      throwError "Required actual source path absent: {name}"
    let mut path := [name]
    let mut next := name
    while next != root do
      let some previous := parent[next]? | throwError "Broken dependency path"
      path := previous::path
      next := previous
    logInfo m!"SOURCE_PATH {String.intercalate " -> " (path.map toString)}"
  for name in forbidden do
    if seen.contains name then
      throwError "Old numerical/certificate shortcut remains: {name}"
    logInfo m!"ABSENT_SHORTCUT {name}"
  logInfo m!"COMPLETE_CONSTANT_DEPENDENCY_INSPECTION {seen.size}"
#print axioms RamanujanPV.FiniteGuardedMillion.source_fixed
#print axioms RamanujanPV.FiniteGuardedMillion.complete_certificate
#print axioms RamanujanPV.FiniteGuardedMillion.first_1000001_real_interval
#print axioms RamanujanPV.FiniteGuardedMillion.uniform_gap
