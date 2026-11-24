/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import Lean.Util.FoldConsts
import Solution
open Lean Elab Command
private partial def parameterUses : Lean.Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []
run_cmd do
  let env ← getEnv
  let pairs := #[( `PrimePowerPopulation.v1.challenge_cube_population_all_real,
      `RHOnePrime.PowerPopulation.cube_population),
    (`PrimePowerPopulation.v1.challenge_cube_density_all_real,
      `RHOnePrime.PowerPopulation.cube_density_070),
    (`PrimePowerPopulation.v1.challenge_cube_density_natural,
      `RHOnePrime.PowerPopulation.cube_density_070_natural),
    (`PrimePowerPopulation.v1.challenge_higher_power_population,
      `RHOnePrime.PowerPopulation.higher_power_population),
    (`PrimePowerPopulation.v1.challenge_cube_frontier,
      `RHOnePrime.PowerPopulation.cube_population_frontier_070),
    (`PrimePowerPopulation.v1.challenge_density_improves_648,
      `RHOnePrime.PowerPopulation.density_070_improves_648)]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (root, expected) in pairs do
    let some (.thmInfo info) := env.find? root | throwError "Missing canonical theorem {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard canonical axiom {root}: {axs}"
    let constants := info.value.getUsedConstants
    unless constants.contains expected do throwError "Expected power theorem not consumed {root}: {expected}"
    let ps := parameterUses info.value
    unless ps.all (fun p => p.2) do throwError "Unused canonical parameter {root}: {ps}"
    let row := Json.mkObj [("name",toJson root.toString),
      ("expected_consumed_theorem",toJson expected.toString),
      ("axioms",toJson (axs.map Name.toString)),
      ("direct_value_constants",toJson (constants.map Name.toString)),
      ("lambda_parameters",toJson (ps.map fun (name,used) =>
        Json.mkObj [("name",toJson name),("used_in_body",toJson used)]))]
    logInfo m!"RH_POWER_CANONICAL_THEOREM {row.compress}"
  logInfo m!"RH_POWER_CANONICAL_AUDIT_PASS {pairs.size}"
