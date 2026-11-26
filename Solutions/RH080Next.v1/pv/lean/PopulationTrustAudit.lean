/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PopulationSourceFinal
import PopulationControl
import PopulationNodes
import PopulationMutations
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
    `RH080Next.PopulationPV.source_first_periodic_norm,
    `RH080Next.PopulationPV.source_output_periodic_norm,
    `RH080Next.PopulationPV.actual_source_output,
    `RH080Next.PopulationPV.actual_source_syntax,
    `RH080Next.PopulationPV.actual_main_output,
    `RH080Next.PopulationPV.Execution.actual_norm_program,
    `RH080Next.PopulationPV.Model.actual_grid_enclosure,
    `RH080Next.PopulationPV.Model.periodic_norm_upper,
    `RH080Next.PopulationPV.kernel_only_periodic_norm,
    `RH080Next.PopulationPV.polynomial_identity,
    `RH080Next.PopulationPV.sine_constant_rejected,
    `RH080Next.PopulationPV.grid_bound_rejected,
    `RH080Next.PopulationPV.rounding_allowance_rejected]
  for root in roots do
    let some (.thmInfo _) := env.find? root | throwError "Missing theorem {root}"
    let axioms ← collectAxioms root
    unless axioms.all allowed.contains do throwError "Forbidden transitive axiom {root}: {axioms}"
    logInfo m!"POPULATION_AXIOMS {root}: {axioms}"
  let edges := #[
    (`RH080Next.PopulationPV.source_first_periodic_norm,`RH080Next.PopulationPV.actual_source_output),
    (`RH080Next.PopulationPV.source_first_periodic_norm,`RH080Next.PopulationPV.source_output_periodic_norm),
    (`RH080Next.PopulationPV.actual_source_output,`RH080Next.PopulationPV.actual_source_syntax),
    (`RH080Next.PopulationPV.actual_source_output,`RH080Next.PopulationPV.actual_main_output),
    (`RH080Next.PopulationPV.actual_main_output,`RH080Next.PopulationPV.Execution.actual_norm_program),
    (`RH080Next.PopulationPV.actual_main_output,`RH080Next.PopulationPV.actual_main_shape),
    (`RH080Next.PopulationPV.checkedSyntax_sound,`GoldbachDirect.Correspondence.supportedProgramSyntax_sound)]
  for (parent,child) in edges do
    let some info := env.find? parent | throwError "Missing proof parent {parent}"
    let some value := proofValue? info | throwError "No proof body {parent}"
    unless value.getUsedConstants.contains child do throwError "Missing proof edge {parent}->{child}"
    logInfo m!"POPULATION_EDGE {parent}->{child}"
  let c := valueClosure env [`RH080Next.PopulationPV.source_first_periodic_norm]
  for required in #[`RH080Next.PopulationPV.Execution.actual_norm_program,
    `RH080Next.PopulationPV.actual_source_syntax,
    `RH080Next.PopulationPV.Model.actual_grid_enclosure,
    `RH080Next.PopulationPV.Model.periodic_norm_upper] do
    unless c.contains required do throwError "Source theorem omitted required proof {required}"
  unless !c.contains `RH080Next.PopulationPV.kernel_only_periodic_norm do
    throwError "Matched-control theorem substituted for actual source execution"
  let d := valueClosure env [`RH080Next.PopulationPV.kernel_only_periodic_norm]
  for forbidden in #[`RH080Next.PopulationPV.Execution.actual_norm_program,
    `RH080Next.PopulationPV.actual_source_output,
    `RH080Next.PopulationPV.actual_source_syntax,
    `RH080Next.PopulationPV.actual_main_output] do
    if d.contains forbidden then throwError "C source entered matched kernel-only control {forbidden}"
  let some info := env.find? `RH080Next.PopulationPV.source_output_periodic_norm |
    throwError "Missing unknown-output transport"
  let some body := proofValue? info | throwError "Missing output transport body"
  unless (leadingUses body).any (fun item => item.1=="h" && item.2) do
    throwError "Actual source-output premise was not consumed"
  logInfo "POPULATION_TRUST_AUDIT_PASS roots=13 edges=7 source-execution-consumed matched-control-source-free no-native no-sorry"
