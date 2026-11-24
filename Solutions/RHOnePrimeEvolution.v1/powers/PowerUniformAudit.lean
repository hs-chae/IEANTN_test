/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import Lean.Util.FoldConsts
import PowerAudit
import UniformCubeNatural
open Lean Elab Command
private partial def parameterUses : Lean.Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []
run_cmd do
  let env ← getEnv
  let mods := #["CubeDensityUniform", "UniformCubeNatural"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    if !mods.contains modName.toString then continue
    let some (.thmInfo _) := env.find? name | continue
    let axs ← collectAxioms name
    unless axs.all allowed.contains do throwError "Nonstandard axiom {name}: {axs}"
    let row := Json.mkObj [("name",toJson name.toString),("module",toJson modName.toString),
      ("axioms",toJson (axs.map Name.toString))]
    logInfo m!"RH_POWER_UNIFORM_THEOREM {row.compress}"
    count := count + 1
  unless count > 5 do throwError "Missing complete power development"
  logInfo m!"RH_POWER_UNIFORM_AUDIT_PASS {count}"
run_cmd do
  let env ← getEnv
  let roots := #[`RHOnePrime.PowerPopulation.cube_density_648_from_sources,
    `RHOnePrime.PowerPopulation.cube_population_frontier_from_sources,
    `RHOnePrime.PowerPopulation.cube_density_648_natural_from_sources]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing final theorem {root}"
    let constants := info.value.getUsedConstants
    unless constants.contains `RHOcticPush.OptimizedFinal.strict_count_family do
      throwError "Source-count provider not consumed: {root}"
    let ps := parameterUses info.value
    unless ps.all (fun p => p.2) do throwError "Unused final input {root}: {ps}"
    let row := Json.mkObj [("name",toJson root.toString),
      ("direct_value_constants",toJson (constants.map Name.toString)),
      ("lambda_parameters",toJson (ps.map fun (name,used) =>
        Json.mkObj [("name",toJson name),("used_in_body",toJson used)]))]
    logInfo m!"RH_POWER_UNIFORM_BODY {row.compress}"
