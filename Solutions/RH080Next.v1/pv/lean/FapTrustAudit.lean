/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FapSourceFinal
import Lean
set_option autoImplicit false
set_option maxRecDepth 1000000
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
      | some info => match proofValue? info with
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
    `RH080Next.FapPV.actual_source_scalar_output,
    `RH080Next.FapPV.source_output_finite_specification,
    `RH080Next.FapPV.source_output_mathematical_boundaries,
    `RH080Next.FapPV.source_first_nodal_boundaries,
    `RH080Next.FapPV.actual_main_output,
    `RH080Next.FapPV.actual_source_syntax,
    `RH080Next.FapPV.checkedSyntax_sound,
    `RH080Next.FapPV.Execution.actual_f0_numerator,
    `RH080Next.FapPV.Execution.actual_positive_area_numerator,
    `RH080Next.FapPV.Execution.actual_component_height,
    `RH080Next.FapPV.Execution.actual_first_variation_numerator,
    `RH080Next.FapPV.Execution.actual_derivative_variation_numerator,
    `RH080Next.FapPV.Execution.actual_second_moment_numerator,
    `RH080Next.FapPV.Execution.actual_maximum_numerator]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden transitive axiom {root}: {axioms}"
    logInfo m!"WINDOW_AXIOMS {root}: {axioms}"
  let edges := #[
    (`RH080Next.FapPV.actual_source_scalar_output,`RH080Next.FapPV.actual_source_syntax),
    (`RH080Next.FapPV.actual_source_scalar_output,`RH080Next.FapPV.actual_main_output),
    (`RH080Next.FapPV.source_first_nodal_boundaries,`RH080Next.FapPV.source_output_mathematical_boundaries),
    (`RH080Next.FapPV.source_first_nodal_boundaries,`RH080Next.FapPV.actual_source_scalar_output),
    (`RH080Next.FapPV.actual_main_output,`RH080Next.FapPV.Execution.actual_f0_numerator),
    (`RH080Next.FapPV.actual_main_output,`RH080Next.FapPV.Execution.actual_positive_area_numerator),
    (`RH080Next.FapPV.actual_main_output,`RH080Next.FapPV.Execution.actual_component_height),
    (`RH080Next.FapPV.actual_main_output,`RH080Next.FapPV.Execution.actual_first_variation_numerator),
    (`RH080Next.FapPV.actual_main_output,`RH080Next.FapPV.Execution.actual_derivative_variation_numerator),
    (`RH080Next.FapPV.actual_main_output,`RH080Next.FapPV.Execution.actual_second_moment_numerator),
    (`RH080Next.FapPV.actual_main_output,`RH080Next.FapPV.Execution.actual_maximum_numerator)]
  for (parent,child) in edges do
    let some info := env.find? parent | throwError "Missing proof parent {parent}"
    let some value := proofValue? info | throwError "Missing proof body {parent}"
    unless value.getUsedConstants.contains child do throwError "Missing proof edge {parent}->{child}"
    logInfo m!"WINDOW_EDGE {parent}->{child}"
  let closure := valueClosure env [`RH080Next.FapPV.source_first_nodal_boundaries]
  let required := #[`RH080Next.FapPV.actual_source_syntax,
    `RH080Next.FapPV.Execution.actual_f0_numerator,
    `RH080Next.FapPV.Execution.actual_positive_area_numerator,
    `RH080Next.FapPV.Execution.actual_component_height,
    `RH080Next.FapPV.Execution.actual_first_variation_numerator,
    `RH080Next.FapPV.Execution.actual_derivative_variation_numerator,
    `RH080Next.FapPV.Execution.actual_second_moment_numerator,
    `RH080Next.FapPV.Execution.actual_maximum_numerator,
    `RH080Next.FapPV.actual_qF0,`RH080Next.FapPV.actual_qH,
    `RH080Next.FapPV.actual_qV1,`RH080Next.FapPV.actual_qMu2]
  for theoremName in required do
    unless closure.contains theoremName do throwError "Required proof absent {theoremName}"
  let some info := env.find? `RH080Next.FapPV.source_output_mathematical_boundaries |
    throwError "Missing output transport"
  let some body := proofValue? info | throwError "Missing output transport proof"
  unless (leadingUses body).any (fun item => item.1=="h" && item.2) do
    throwError "Unknown actual source output premise not consumed"
  logInfo "WINDOW_TRUST_AUDIT_PASS roots=14 edges=11 all-seven-source-executions-consumed four-actual-nodal-boundaries no-native no-sorry"
