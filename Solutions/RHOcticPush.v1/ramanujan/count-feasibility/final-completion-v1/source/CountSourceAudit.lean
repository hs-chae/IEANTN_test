import CountSourceFinal
import Lean
open Lean Elab Command

run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "COUNTER_AUDIT_PROGRESS.txt" "begin theorem census"
  let owned := #["SourceOutputAdapter","DecodedOutputs","HighDecodedOutputs","CountSourceFinal"]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  let mut count : Nat := 0
  for (name,idx) in env.const2ModIdx.toList do
    let mod := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !owned.contains mod.toString then continue
    let some (.thmInfo _) := env.find? name | continue
    liftIO <| IO.FS.writeFile "COUNTER_AUDIT_PROGRESS.txt" ("axioms:"++name.toString)
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "Nonstandard source-grammar axiom {name}: {axioms}"
    logInfo m!"COLD_SOURCE_THEOREM {(Json.mkObj [("name",toJson name.toString),("module",toJson mod.toString),("axioms",toJson (axioms.map Name.toString))]).compress}"
    count := count+1
  unless count > 0 do throwError "Empty grammar audit"
  logInfo m!"COLD_SOURCE_AUDIT_PASS {count}"
  let root := `RHOcticPush.ColdCount.complete_actual_source_run
  -- Exact finite proof-value edge matrix, not an unbounded old-proof traversal.
  -- Endpoints are stated explicitly; full axiom closure remains checked above.
  let edges : Array (Name × Array Name) := #[
    (`RHOcticPush.ColdCount.complete_actual_source_run,#[`RHOcticPush.SourceOutputAdapter.canonical_source_output,`RHOcticPush.ColdCount.count]),
    (`RHOcticPush.ColdCount.count,#[`RamanujanPV.HighTransitionCount.pi_1490000000000]),
    (`RHOcticPush.SourceOutputAdapter.canonical_source_output,#[`RHOcticPush.CounterSyntax.complete_canonical_source_run]),
    (`RHOcticPush.CounterSyntax.complete_canonical_source_run,#[`RHOcticPush.CounterSyntax.possible_source_success]),
    (`RHOcticPush.CounterSyntax.possible_source_success,#[`RHOcticPush.CounterSyntax.actual_source_model_main,`RHOcticPush.CounterSyntax.checkedCounter_sound,`RHOcticPush.CounterSyntax.checkedDriver_sound]),
    (`RHOcticPush.CounterSyntax.actual_source_model_main,#[`RHOcticPush.CounterSyntax.actual_counter_accepted,`RHOcticPush.CounterSyntax.actual_driver_accepted,`RHOcticPush.HighDriverContract.actual_source_model_main]),
    (`RHOcticPush.CounterSyntax.actual_counter_accepted,#[`RHOcticPush.CounterSyntax.actual_counter_profile,`RHOcticPush.CounterSyntax.actual_counter_render]),
    (`RHOcticPush.CounterSyntax.actual_counter_render,#[`RamanujanPV.QuotientCSourceV2.actual_source_bytes]),
    (`RHOcticPush.CounterSyntax.actual_driver_accepted,#[`RHOcticPush.CounterSyntax.actual_driver_profile,`RHOcticPush.HighDriverSource.actual_source_bytes]),
    (`RHOcticPush.CounterSyntax.checkedCounter_sound,#[`RHOcticPush.CounterSyntax.counter_render_sound]),
    (`RHOcticPush.CounterSyntax.counter_render_sound,#[`RHOcticPush.CounterSyntax.functions_sound]),
    (`RHOcticPush.CounterSyntax.functions_sound,#[`RHOcticPush.CounterSyntax.function_sound]),
    (`RHOcticPush.CounterSyntax.function_sound,#[`RHOcticPush.CounterSyntax.statement_sound]),
    (`RHOcticPush.CounterSyntax.statement_sound,#[`RHOcticPush.CounterSyntax.expression_sound]),
    (`RHOcticPush.CounterSyntax.checkedDriver_sound,#[`RHOcticPush.CounterSyntax.driver_render_sound]),
    (`RHOcticPush.CounterSyntax.driver_render_sound,#[`RHOcticPush.CounterSyntax.function_sound])]
  for (fromName,targets) in edges do
    let some info := env.find? fromName | throwError "Missing edge theorem {fromName}"
    let some value := info.value? true | throwError "Missing theorem VALUE {fromName}"
    liftIO <| IO.FS.writeFile "COUNTER_AUDIT_PROGRESS.txt" ("value:"++fromName.toString)
    let used := value.getUsedConstants
    for target in targets do
      unless used.contains target do throwError "Unchecked VALUE edge {fromName} -> {target}"
  liftIO <| IO.FS.writeFile "COUNTER_AUDIT_PROGRESS.txt" "checked all direct edges; reachability"
  let mut reached : NameSet := {}
  let mut pending : List Name := [root]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if reached.contains name then continue
    reached := reached.insert name
    for (fromName,targets) in edges do
      if fromName == name then pending := targets.toList++pending
  let required := #[`RamanujanPV.HighTransitionCount.pi_1490000000000,`RHOcticPush.CounterSyntax.checkedCounter_sound,
    `RHOcticPush.CounterSyntax.checkedDriver_sound,
    `RHOcticPush.CounterSyntax.counter_render_sound,
    `RHOcticPush.CounterSyntax.driver_render_sound,
    `RHOcticPush.CounterSyntax.expression_sound,
    `RHOcticPush.CounterSyntax.statement_sound,
    `RHOcticPush.CounterSyntax.actual_counter_profile,
    `RHOcticPush.CounterSyntax.actual_driver_profile,
    `RamanujanPV.QuotientCSourceV2.actual_source_bytes,
    `RHOcticPush.HighDriverSource.actual_source_bytes,
    `RHOcticPush.HighDriverContract.actual_source_model_main]
  for name in required do
    unless reached.contains name do throwError "Final source-run value does not consume {name}"
  logInfo m!"COLD_SOURCE_VALUE_PATH {(Json.mkObj [("root",toJson root.toString),("required",toJson (required.map Name.toString)),("required_count",toJson required.size),("reached_application_and_boundary_constants",toJson reached.size),("checked_value_edges",toJson (edges.foldl (fun n e => n+e.2.size) 0))]).compress}"
