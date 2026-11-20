/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.SegmentSourceMargins
import Lean.Util.FoldConsts

/-! Executed environment inspection. This emits evidence about actual proof
constants; it adds no mathematical theorem or proof axiom. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let root := ``RamanujanPV.SegmentSourceMargins.million_gap
  let required := [``RamanujanPV.SegmentCFunction.positive_output_sound,
    ``RamanujanPV.SegmentCFunction.correct_claims_execution,
    ``RamanujanPV.SegmentNetwork.source_count_at,
    ``RamanujanPV.SegmentTableProvider.source_provider,
    ``RamanujanPV.SegmentWindowCells.complete_certificate]
  let forbidden := [``RamanujanPV.PrimeWindow.count_at,
    ``RamanujanPV.PrimeWindow.source_count_at,
    ``RamanujanPV.WindowCells.row_counts,
    ``RamanujanPV.WindowCells.complete_certificate,
    ``RamanujanPV.LocalWindowMillion.p_increment,
    ``RamanujanPV.LocalWindowMillion.q_increment,
    ``RamanujanPV.LocalCellsMillion.conditional_certificate,
    ``RamanujanPV.LocalCellsMillion.conditional_holds]
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut parent : Std.HashMap Name Name := {}
  let mut pending := [root]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    let some info := env.find? name | throwError "Missing inspected constant {name}"
    for dependency in info.getUsedConstantsAsSet.toList do
      if !seen.contains dependency then
        seen := seen.insert dependency
        parent := parent.insert dependency name
        pending := dependency::pending
  for name in required do
    unless seen.contains name do
      throwError "Actual source checker missing from selected proof path: {name}"
    let mut path := [name]
    let mut next := name
    while next != root do
      let some previous := parent[next]? | throwError "Broken dependency path"
      path := previous::path
      next := previous
    logInfo m!"SOURCE_PATH {String.intercalate " -> " (path.map toString)}"
  for name in forbidden do
    if seen.contains name then
      throwError "Direct local cardinality shortcut remains in selected proof: {name}"
    logInfo m!"ABSENT_SHORTCUT {name}"
  logInfo m!"COMPLETE_CONSTANT_DEPENDENCY_INSPECTION {seen.size}"

#print axioms RamanujanPV.SegmentSourceMargins.million_gap
