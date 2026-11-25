/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import SameSourceSolution
open Lean Elab Command
private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ b _ => (n.toString,b.hasLooseBVar 0)::leadingUses b
  | .mdata _ b => leadingUses b
  | _ => []
run_cmd do
  let env←getEnv
  let targets:=#[
    (`PrimePowerPopulation.v2.challenge_cube_density_all_real,#[`RH080.SameSource.cube_density_078146],#["hf"]),
    (`PrimePowerPopulation.v2.challenge_single_window_cube,#[`RH080.SameSource.single_window_078146],#["hf"]),
    (`PrimePowerPopulation.v2.challenge_equal_cell_cube,#[`RH080.SameSource.tiled_0789],#["hf"]),
    (`PrimePowerPopulation.v2.challenge_equal_cell_cube_late,#[`RH080.SameSource.tiled_0804_late],#["hf"]),
    (`PrimePowerPopulation.v2.challenge_cube_density_natural,#[`PrimePowerPopulation.v2.challenge_cube_density_all_real],#["hf"]),
    (`PrimePowerPopulation.v2.challenge_retains_070_all_real,#[`PrimePowerPopulation.v2.challenge_cube_density_all_real,`PrimePowerPopulation.v2.challenge_strict_coefficient_gain],#["hf"]),
    (`PrimePowerPopulation.v2.challenge_strict_coefficient_gain,#[`Real.exp_pos],#[]),
    (`RH080.SameSource.cube_density_078146,#[`RH080.SameSource.single_window_078146,`RH080.SameSource.tiled_0789],#["hf"]),
    (`RH080.SameSource.tiling_lower,#[`RH080.SameSource.exact_cell_common_lower,`RH080.SameSource.tiled_count],#["hf"]),
    (`RH080.SameSource.single_window_078146,#[`RH080.SameSource.error_budget8,`RH080.SameSource.error_budget801],#["hf"])]
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  for (root,providers,parameters) in targets do
    let some (.thmInfo info):=env.find? root | throwError "Missing actual theorem {root}"
    let axs←collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard axiom {root}: {axs}"
    let constants:=info.value.getUsedConstants
    for provider in providers do
      unless constants.contains provider do throwError "Expected proof-value provider missing {root}->{provider}"
    let uses:=leadingUses info.value
    for p in parameters do
      unless uses.any (fun r=>r.1==p && r.2) do throwError "Original Octic input not consumed {root}:{p}"
    logInfo m!"SAME_SOURCE_AUDIT {Json.mkObj [("root",toJson root.toString),("providers",toJson (providers.map Name.toString)),("axioms",toJson (axs.map Name.toString)),("input_uses",toJson (uses.map fun (n,u)=>Json.mkObj [("parameter",toJson n),("used",toJson u)])),("value_constants",toJson (constants.map Name.toString))]}"
  logInfo "SAME_SOURCE_AUDIT_PASS_10"
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v2.cube_density_all_real := PrimePowerPopulation.v2.challenge_cube_density_all_real
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v2.single_window_cube := PrimePowerPopulation.v2.challenge_single_window_cube
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v2.equal_cell_cube := PrimePowerPopulation.v2.challenge_equal_cell_cube
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v2.equal_cell_cube_late := PrimePowerPopulation.v2.challenge_equal_cell_cube_late
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v2.cube_density_natural := PrimePowerPopulation.v2.challenge_cube_density_natural
example : PrimeInterval.v4.optimized_strict_family → PrimePowerPopulation.v2.retains_070_all_real := PrimePowerPopulation.v2.challenge_retains_070_all_real
example : PrimePowerPopulation.v2.strict_coefficient_gain := PrimePowerPopulation.v2.challenge_strict_coefficient_gain
example : PrimePowerPopulation.v2.cube_density_all_real=(∀ n:ℝ,Real.exp 8≤n →(39073/50000:ℝ)*n^2/Real.log n<((IEANTN.PrimeWindows.primesBetween (n^3) ((n+1)^3)).card:ℝ)):=rfl
example : RH080.SameSource.C0=(fun n:ℝ=>((n+1)^3-n^3)/(3*n*Real.sqrt n*Real.log n)):=rfl
example : RH080.SameSource.cells=(fun n:ℝ=>⌈RH080.SameSource.C0 n/16⌉₊):=rfl
example : IEANTN.PrimeWindows.primesBetween=(fun a b:ℝ=>(Nat.primesLE ⌊b⌋₊).filter fun p:ℕ=>a<(p:ℝ) ∧ (p:ℝ)<b):=rfl
