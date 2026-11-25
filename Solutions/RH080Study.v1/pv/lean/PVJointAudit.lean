/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import CompactDualSourceFirst
import DualSineExecution
import Lean

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean Elab Command

private def proofValue? : ConstantInfo → Option Expr
  | .thmInfo info => some info.value
  | .defnInfo info => some info.value
  | _ => none

private partial def valueClosure (env : Environment) (queue : List Name)
    (visited : NameSet := {}) : NameSet :=
  match queue with
  | [] => visited
  | name::rest =>
    if visited.contains name then valueClosure env rest visited
    else
      let visited := visited.insert name
      match env.find? name with
      | some info =>
        match proofValue? info with
        | some value => valueClosure env (value.getUsedConstants.toList ++ rest) visited
        | none => valueClosure env rest visited
      | none => valueClosure env rest visited

private partial def leadingUses : Expr → List (String × Bool)
  | .lam name _ body _ => (name.toString,body.hasLooseBVar 0)::leadingUses body
  | .mdata _ body => leadingUses body
  | _ => []

run_cmd do
  let env ← getEnv
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  let roots := #[
    `RH080.Dual.actual_source_first_functional_result,
    `RH080.Dual.source_first_compact_global,
    `RH080.Dual.source_first_compact_obstruction,
    `RH080PV.Verified.actual_source_first_output,
    `RH080PV.Verified.actual_source_grid_cap,
    `RH080PV.Verified.source_result_controls_grid,
    `RH080PV.Execution.actual_numerical_execution,
    `RH080PV.actual_source_syntax,
    `RH080PV.checkedSyntax_sound,
    `RH080PV.Output.actual_host_main,
    `RH080PV.Output.actual_successful_capture,
    `RH080PV.Model.actual_sine_source_model,
    `RH080PV.Grid.true_grid_samples]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing actual theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden transitive axiom {root}: {axioms}"
    logInfo m!"PV_AXIOMS {root}: {axioms}"
  let edges := #[
    (`RH080.Dual.actual_source_first_functional_result,`RH080PV.Verified.actual_source_first_output),
    (`RH080.Dual.actual_source_first_functional_result,`RH080.Dual.source_first_compact_obstruction),
    (`RH080.Dual.source_first_compact_global,`RH080PV.Verified.actual_source_grid_cap),
    (`RH080.Dual.source_first_compact_obstruction,`RH080PV.Verified.actual_source_grid_cap),
    (`RH080PV.Verified.actual_source_grid_cap,`RH080PV.Verified.source_result_controls_grid),
    (`RH080PV.Verified.actual_source_grid_cap,`RH080PV.Execution.actual_numerical_execution),
    (`RH080PV.Verified.actual_source_first_output,`RH080PV.actual_source_syntax),
    (`RH080PV.Verified.actual_source_first_output,`RH080PV.Output.actual_host_main),
    (`RH080PV.actual_source_syntax,`RH080PV.checkedSyntax_sound),
    (`RH080PV.checkedSyntax_sound,`GoldbachDirect.Correspondence.supportedProgramSyntax_sound),
    (`RH080PV.Output.actual_host_main,`RH080PV.Execution.actual_numerical_execution)]
  for (parent,child) in edges do
    let some info := env.find? parent | throwError "Missing value parent {parent}"
    let some value := proofValue? info | throwError "Missing proof body {parent}"
    unless value.getUsedConstants.contains child do throwError "Missing actual proof-value edge {parent}->{child}"
    logInfo m!"PV_EDGE {parent}->{child}"
  for root in #[`RH080.Dual.source_first_compact_global,`RH080.Dual.source_first_compact_obstruction] do
    let closure := valueClosure env [root]
    for forbidden in #[`RH080PV.Model.sampleBound_all,
      `RH080.Dual.kernel_compact_global,`RH080.Dual.kernel_compact_obstruction] do
      if closure.contains forbidden then throwError "D-only shortcut entered C consumer {root}->{forbidden}"
    unless closure.contains `RH080PV.Execution.actual_numerical_execution do
      throwError "Actual numerical C execution not consumed {root}"
    logInfo m!"PV_CLOSURE_SOURCE_EXECUTION_CONSUMED {root}"
  let some info := env.find? `RH080PV.Verified.source_result_controls_grid |
    throwError "Missing output transport"
  let some body := proofValue? info | throwError "Missing output transport body"
  unless (leadingUses body).any (fun item => item.1=="run" && item.2) do
    throwError "Unknown-cap source execution premise not used"
  logInfo "PV_JOINT_AUDIT_PASS roots=13 edges=11 no-native no-sorry no-D-cap-shortcut"

example : RH080.Dual.SourceFirstFunctionalResult :=
  RH080.Dual.actual_source_first_functional_result
