/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import ParetoSolution
open Lean Elab Command
private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ b _ => (n.toString,b.hasLooseBVar 0)::leadingUses b
  | .mdata _ b => leadingUses b
  | _ => []
run_cmd do
  let env←getEnv
  let targets:=#[
    (`ThetaCubePopulation.v2.challenge_cube_density_09669924,#[`RH080.Pareto966.cube_density_09669924],#["hRH","hS","h₁","h₂"]),
    (`ThetaCubePopulation.v2.challenge_cube_density_09669924_natural,#[`ThetaCubePopulation.v2.challenge_cube_density_09669924],#["hRH","hS","h₁","h₂"]),
    (`ThetaCubePopulation.v2.challenge_finite_seam_098,#[`RH080.Pareto966.finite_098],#["h₁","h₂"]),
    (`ThetaCubePopulation.v2.challenge_strict_gain_on_common_ray,#[`Real.exp_pos],#[]),
    (`ThetaCubePopulation.v2.challenge_retains_0965,#[],#["hOld"]),
    (`RH080.Pareto966.cube_density_09669924,#[`RH080.Pareto966.finite_098,`RH080.Pareto966.count_budget,`RH080.Pareto966.main_gain,`RH080.Pareto966.endpoint_allowance,`RH080.Pareto966.seam_budget,`RH080.Pareto966.late_budget],#["hB","hS","hRH"]),
    (`RH080.Pareto966.count_budget,#[`RH080.Pareto966.source_error_budget,`RH080.Estimates.cube_count_schoenfeld_explicit],#["hS","hRH"]),
    (`RH080.Pareto966.seam_budget,#[`RH080.Pareto966.polynomial_budget,`RH080.Pareto966.log_anchor1],#[])]
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  for (root,providers,parameters) in targets do
    let some (.thmInfo info):=env.find? root | throwError "Missing actual theorem {root}"
    let axs←collectAxioms root
    unless axs.all allowed.contains do throwError "Unaccepted axiom {root}: {axs}"
    let cs:=info.value.getUsedConstants
    for p in providers do
      unless cs.contains p do throwError "Expected proof-value provider missing {root}->{p}"
    let uses:=leadingUses info.value
    for p in parameters do
      unless uses.any (fun r=>r.1==p && r.2) do throwError "Required source input not consumed {root}:{p}"
    logInfo m!"PARETO_AUDIT {Json.mkObj [("root",toJson root.toString),("providers",toJson (providers.map Name.toString)),("axioms",toJson (axs.map Name.toString)),("input_uses",toJson (uses.map fun (n,u)=>Json.mkObj [("parameter",toJson n),("used",toJson u)])),("value_constants",toJson (cs.map Name.toString))]}"
  logInfo "PARETO_AUDIT_PASS_8"
example : RH.v1.hypothesis → SchoenfeldRHTheta.v1.refined_theta → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → ThetaCubePopulation.v2.cube_density_09669924:=ThetaCubePopulation.v2.challenge_cube_density_09669924
example : RH.v1.hypothesis → SchoenfeldRHTheta.v1.refined_theta → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → ThetaCubePopulation.v2.cube_density_09669924_natural:=ThetaCubePopulation.v2.challenge_cube_density_09669924_natural
example : Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → ThetaCubePopulation.v2.finite_seam_098:=ThetaCubePopulation.v2.challenge_finite_seam_098
example : ThetaCubePopulation.v2.strict_gain_on_common_ray:=ThetaCubePopulation.v2.challenge_strict_gain_on_common_ray
example : ThetaCubePopulation.v1.cube_density_0965 → ThetaCubePopulation.v2.retains_0965:=ThetaCubePopulation.v2.challenge_retains_0965
example : ThetaCubePopulation.v2.cube_density_09669924=(∀ n:ℝ,Real.exp 8≤n →(2417481/2500000:ℝ)*n^2/Real.log n<((IEANTN.ThetaWindows.openPrimes (n^3) ((n+1)^3)).card:ℝ)):=rfl
example : ThetaCubePopulation.v2.retains_0965=ThetaCubePopulation.v1.cube_density_0965:=rfl
example : IEANTN.ThetaWindows.openPrimes=(fun a b:ℝ=>(Nat.primesLE ⌊b⌋₊).filter fun p:ℕ=>a<(p:ℝ) ∧ (p:ℝ)<b):=rfl
