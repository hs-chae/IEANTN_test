/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import EarlySolution
open Lean Elab Command
private partial def leadingUses : Expr → List (String × Bool)
 | .lam n _ b _ => (n.toString,b.hasLooseBVar 0)::leadingUses b
 | .mdata _ b => leadingUses b
 | _ => []
run_cmd do
 let env←getEnv
 let targets:=#[
  (`ThetaCubePopulation.v3.challenge_cube_density_096699_from_369,#[`CubeTheta.cube_hybrid_096699],#["hRH","hS","h₁","h₂"]),
  (`ThetaCubePopulation.v3.challenge_cube_density_096699_natural,#[`ThetaCubePopulation.v3.challenge_cube_density_096699_from_369],#["hRH","hS","h₁","h₂"]),
  (`ThetaCubePopulation.v3.challenge_hybrid_density,#[],#["hEarly","hLate"]),
  (`ThetaCubePopulation.v3.challenge_strict_gain_on_common_ray,#[`Real.exp_pos],#[]),
  (`CubeTheta.cube_hybrid_096699,#[`CubeTheta.buthe_fixed,`CubeTheta.schoenfeld_density],#["hS","rh","hB"]),
  (`CubeTheta.endpoint_transfer,#[],#[])]
 for (root,providers,parameters) in targets do
  let some (.thmInfo info):=env.find? root | throwError "Missing actual theorem {root}"
  let axs←collectAxioms root
  unless axs.all (#[`propext,`Classical.choice,`Quot.sound].contains) do
   throwError "Unaccepted axiom {root}: {axs}"
  let cs:=info.value.getUsedConstants
  for p in providers do
   unless cs.contains p do throwError "Expected proof-value provider missing {root}->{p}"
  let uses:=leadingUses info.value
  for p in parameters do
   unless uses.any (fun r=>r.1==p && r.2) do throwError "Required source input not consumed {root}:{p}"
  logInfo m!"EARLY369_ACTUAL_TYPE {root}: {info.type}"
  logInfo m!"EARLY369_AUDIT {Json.mkObj [("root",toJson root.toString),("axioms",toJson (axs.map Name.toString)),("input_uses",toJson (uses.map fun (n,u)=>Json.mkObj [("parameter",toJson n),("used",toJson u)])),("value_constants",toJson (cs.map Name.toString))]}"
 logInfo "EARLY369_AUDIT_PASS_6"
example : RH.v1.hypothesis → SchoenfeldRHTheta.v1.refined_theta → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → ThetaCubePopulation.v3.cube_density_096699_from_369 := ThetaCubePopulation.v3.challenge_cube_density_096699_from_369
example : RH.v1.hypothesis → SchoenfeldRHTheta.v1.refined_theta → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → ThetaCubePopulation.v3.cube_density_096699_natural := ThetaCubePopulation.v3.challenge_cube_density_096699_natural
example : ThetaCubePopulation.v3.cube_density_096699_from_369 → ThetaCubePopulation.v2.cube_density_09669924 → ThetaCubePopulation.v3.hybrid_density := ThetaCubePopulation.v3.challenge_hybrid_density
example : ThetaCubePopulation.v3.strict_gain_on_common_ray := ThetaCubePopulation.v3.challenge_strict_gain_on_common_ray
example : ThetaCubePopulation.v3.cube_density_096699_from_369 = (∀ n:ℝ,369≤n → (96699/100000:ℝ)*n^2/Real.log n < ((IEANTN.ThetaWindows.openPrimes (n^3) ((n+1)^3)).card:ℝ)) := rfl
example : IEANTN.ThetaWindows.openPrimes = QuarticWindow.primesBetween := rfl
