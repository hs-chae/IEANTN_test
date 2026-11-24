/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import IEANTNCountConsumer
import Lean

/-! Every displayed VALUE edge must occur in the actual proof term. The IEANTN
endpoint is checked in the theorem's actual type.
Numeric bytes remain kernel-derived; no native/physical execution is inferred. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let root := `RHOcticPush.IEANTNCount.primeCounting_fixed_point
  let owned := #[`RHOcticPush.IEANTNCount.wordBytes_injective_below,
    `RHOcticPush.IEANTNCount.fixed_count_from_same_source_run, root]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in owned do
    let some (.thmInfo _) := env.find? name | throwError "Missing IEANTN theorem {name}"
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do throwError "Unapproved IEANTN theorem axiom {name}: {axioms}"
    logInfo m!"IEANTN_COUNT_AXIOMS {(Json.mkObj [("name",toJson name.toString),("axioms",toJson (axioms.map Name.toString))]).compress}"
  let some rootInfo := env.find? root | throwError "Missing IEANTN endpoint"
  let exactType ← liftTermElabM do
    let expected ← Term.elabType (←
      `(IEANTN.primeCounting ((1490000000000 : Nat) : ℝ) = (55206486339 : ℝ)))
    Term.synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    Meta.isDefEq rootInfo.type expected
  unless exactType do
    throwError "IEANTN theorem is not the exact closed expected target: {rootInfo.type}"
  unless rootInfo.type.getUsedConstants.contains `IEANTN.primeCounting do
    throwError "Final theorem does not mention the actual IEANTN prime-counting definition"
  logInfo m!"IEANTN_COUNT_EXACT_TYPE {rootInfo.type}"
  let edges : Array (Name × Array Name) := #[
    (root, #[`RHOcticPush.IEANTNCount.fixed_count_from_same_source_run]),
    (`RHOcticPush.IEANTNCount.fixed_count_from_same_source_run,
      #[`RHOcticPush.ColdCount.complete_actual_source_run,
        `RHOcticPush.CounterSyntax.every_source_success,
        `RHOcticPush.IEANTNCount.wordBytes_injective_below]),
    (`RHOcticPush.ColdCount.complete_actual_source_run,
      #[`RHOcticPush.SourceOutputAdapter.canonical_source_output,`RHOcticPush.ColdCount.count]),
    (`RHOcticPush.ColdCount.count, #[`RamanujanPV.HighTransitionCount.pi_1490000000000]),
    (`RHOcticPush.SourceOutputAdapter.canonical_source_output,
      #[`RHOcticPush.CounterSyntax.complete_canonical_source_run]),
    (`RHOcticPush.CounterSyntax.complete_canonical_source_run,
      #[`RHOcticPush.CounterSyntax.possible_source_success]),
    (`RHOcticPush.CounterSyntax.possible_source_success,
      #[`RHOcticPush.CounterSyntax.actual_source_model_main,
        `RHOcticPush.CounterSyntax.checkedCounter_sound,`RHOcticPush.CounterSyntax.checkedDriver_sound]),
    (`RHOcticPush.CounterSyntax.every_source_success,
      #[`RHOcticPush.CounterSyntax.actual_source_model_main]),
    (`RHOcticPush.CounterSyntax.actual_source_model_main,
      #[`RHOcticPush.CounterSyntax.actual_counter_accepted,`RHOcticPush.CounterSyntax.actual_driver_accepted,
        `RHOcticPush.HighDriverContract.actual_source_model_main]),
    (`RHOcticPush.CounterSyntax.actual_counter_accepted,
      #[`RHOcticPush.CounterSyntax.actual_counter_profile,`RHOcticPush.CounterSyntax.actual_counter_render]),
    (`RHOcticPush.CounterSyntax.actual_counter_render, #[`RamanujanPV.QuotientCSourceV2.actual_source_bytes]),
    (`RHOcticPush.CounterSyntax.actual_driver_accepted,
      #[`RHOcticPush.CounterSyntax.actual_driver_profile,`RHOcticPush.HighDriverSource.actual_source_bytes]),
    (`RHOcticPush.CounterSyntax.checkedCounter_sound, #[`RHOcticPush.CounterSyntax.counter_render_sound]),
    (`RHOcticPush.CounterSyntax.counter_render_sound, #[`RHOcticPush.CounterSyntax.functions_sound]),
    (`RHOcticPush.CounterSyntax.functions_sound, #[`RHOcticPush.CounterSyntax.function_sound]),
    (`RHOcticPush.CounterSyntax.function_sound, #[`RHOcticPush.CounterSyntax.statement_sound]),
    (`RHOcticPush.CounterSyntax.statement_sound, #[`RHOcticPush.CounterSyntax.expression_sound]),
    (`RHOcticPush.CounterSyntax.checkedDriver_sound, #[`RHOcticPush.CounterSyntax.driver_render_sound]),
    (`RHOcticPush.CounterSyntax.driver_render_sound, #[`RHOcticPush.CounterSyntax.function_sound]),
    (`RHOcticPush.HighDriverContract.actual_source_model_main,
      #[`RHOcticPush.HighDriverRuntime.successful_main_output]),
    (`RHOcticPush.HighDriverRuntime.successful_main_output,
      #[`RHOcticPush.HighDriverRuntime.declaration_result]),
    (`RHOcticPush.HighDriverRuntime.declaration_result, #[`RHOcticPush.HighDriverRuntime.counter_call_exact]),
    (`RHOcticPush.HighDriverRuntime.counter_call_exact,
      #[`RHOcticPush.HighDriverRuntime.driver_call_correct_of_buffers]),
    (`RHOcticPush.HighDriverRuntime.driver_call_correct_of_buffers,
      #[`RamanujanPV.QuotientCFunction.completed_execution_correct])]
  for (fromName, targets) in edges do
    let some info := env.find? fromName | throwError "Missing VALUE-edge theorem {fromName}"
    let some value := info.value? true | throwError "Missing theorem VALUE {fromName}"
    let used := value.getUsedConstants
    for target in targets do
      unless used.contains target do throwError "Missing actual VALUE edge {fromName} -> {target}"
  let mut reached : NameSet := {}
  let mut pending : List Name := [root]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if reached.contains name then continue
    reached := reached.insert name
    for (fromName, targets) in edges do
      if fromName == name then pending := targets.toList ++ pending
  let required := #[`RHOcticPush.ColdCount.complete_actual_source_run,
    `RHOcticPush.SourceOutputAdapter.canonical_source_output,
    `RHOcticPush.CounterSyntax.complete_canonical_source_run,
    `RHOcticPush.CounterSyntax.possible_source_success,
    `RHOcticPush.CounterSyntax.checkedCounter_sound,`RHOcticPush.CounterSyntax.checkedDriver_sound,
    `RHOcticPush.HighDriverRuntime.successful_main_output,
    `RamanujanPV.QuotientCFunction.completed_execution_correct,
    `RamanujanPV.HighTransitionCount.pi_1490000000000,
    `RHOcticPush.IEANTNCount.wordBytes_injective_below]
  for name in required do
    unless reached.contains name do throwError "IEANTN endpoint misses required VALUE path {name}"
  logInfo m!"IEANTN_COUNT_VALUE_PATH {(Json.mkObj [("root",toJson root.toString),("required",toJson (required.map Name.toString)),("checked_edges",toJson (edges.foldl (fun n e => n+e.2.size) 0)),("IEANTN_object_in_checked_type",toJson true),("exact_target_checked",toJson true),("numerical_witness",toJson "Existing exhaustive kernel count; no new native verification"),("physical_trace_claim",toJson false)]).compress}"
