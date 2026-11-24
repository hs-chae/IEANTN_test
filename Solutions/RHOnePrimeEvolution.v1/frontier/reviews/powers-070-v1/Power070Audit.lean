/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import Lean.Util.FoldConsts
import PowerUniformAudit
import CubeNatural070
open Lean Elab Command
private partial def parameterUses : Lean.Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []
run_cmd do
  let env ← getEnv
  let roots := #[`RHOnePrime.PowerPopulation.cube_density_070,
    `RHOnePrime.PowerPopulation.cube_density_070_from_sources,
    `RHOnePrime.PowerPopulation.density_070_improves_648,
    `RHOnePrime.PowerPopulation.cube_population_frontier_070,
    `RHOnePrime.PowerPopulation.cube_population_frontier_070_from_sources,
    `RHOnePrime.PowerPopulation.cube_density_070_natural,
    `RHOnePrime.PowerPopulation.cube_density_070_natural_from_sources]
  let sourceRoots := #[`RHOnePrime.PowerPopulation.cube_density_070_from_sources,
    `RHOnePrime.PowerPopulation.cube_population_frontier_070_from_sources,
    `RHOnePrime.PowerPopulation.cube_density_070_natural_from_sources]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing theorem {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard axiom {root}: {axs}"
    let constants := info.value.getUsedConstants
    let ps := parameterUses info.value
    if sourceRoots.contains root then
      unless constants.contains `RHOcticPush.OptimizedFinal.strict_count_family do
        throwError "Source-count provider not consumed: {root}"
      unless ps.all (fun p => p.2) do throwError "Unused final input {root}: {ps}"
    let row := Json.mkObj [("name",toJson root.toString),
      ("axioms",toJson (axs.map Name.toString)),
      ("direct_value_constants",toJson (constants.map Name.toString)),
      ("lambda_parameters",toJson (ps.map fun (name,used) =>
        Json.mkObj [("name",toJson name),("used_in_body",toJson used)]))]
    logInfo m!"RH_POWER_070_THEOREM {row.compress}"
  logInfo m!"RH_POWER_070_AUDIT_PASS {roots.size}"
