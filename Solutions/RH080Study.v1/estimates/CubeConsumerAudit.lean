/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import ThetaCubeSolution
open Lean Elab Command
private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ b _ => (n.toString,b.hasLooseBVar 0)::leadingUses b
  | .mdata _ b => leadingUses b
  | _ => []
run_cmd do
  let env ← getEnv
  let targets := #[
    (`ThetaCubePopulation.v1.challenge_schoenfeld_cube_curve,`RH080.Estimates.cube_count_schoenfeld_explicit,#["hRH","hS"]),
    (`ThetaCubePopulation.v1.challenge_buthe_cube_curve,`RH080.Estimates.cube_count_buthe_explicit,#["h₁","h₂"]),
    (`ThetaCubePopulation.v1.challenge_cube_density_096,`RH080.Estimates.cube_density_096,#["hRH","hS","h₁","h₂"]),
    (`ThetaCubePopulation.v1.challenge_cube_density_0965,`RH080.Estimates.cube_density_0965,#["hRH","hS","h₁","h₂"]),
    (`ThetaCubePopulation.v1.challenge_cube_density_0965_finite,`RH080.Estimates.cube_density_0965_finite,#["h₁","h₂"]),
    (`ThetaCubePopulation.v1.challenge_cube_density_0965_natural,`ThetaCubePopulation.v1.challenge_cube_density_0965,#["hRH","hS","h₁","h₂"]),
    (`ThetaCubePopulation.v1.challenge_improves_old_coefficient,`Real.exp_pos,#[])]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for (root,provider,parameters) in targets do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard axiom in {root}: {axs}"
    let constants := info.value.getUsedConstants
    unless constants.contains provider do throwError "Expected actual provider missing {root}->{provider}"
    let uses := leadingUses info.value
    for p in parameters do
      unless uses.any (fun r=>r.1==p && r.2) do throwError "Source input not consumed {root}:{p}"
    logInfo m!"THETA_CUBE_AUDIT {Json.mkObj [("root",toJson root.toString),("provider",toJson provider.toString),("axioms",toJson (axs.map Name.toString)),("input_uses",toJson (uses.map fun (n,u)=>Json.mkObj [("parameter",toJson n),("used",toJson u)])),("value_constants",toJson (constants.map Name.toString))]}"
  logInfo "THETA_CUBE_AUDIT_PASS_7"
example : RH.v1.hypothesis → SchoenfeldRHTheta.v1.refined_theta → Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → ThetaCubePopulation.v1.cube_density_0965 := ThetaCubePopulation.v1.challenge_cube_density_0965
example : Buthe.v1.theorem_2_theta → Buthe.v1.theorem_2_theta_lower → ThetaCubePopulation.v1.cube_density_0965_finite := ThetaCubePopulation.v1.challenge_cube_density_0965_finite
example : ThetaCubePopulation.v1.cube_density_0965 = (∀ n : ℝ,Real.exp 6 ≤ n → (193/200:ℝ)*n^2/Real.log n < ((IEANTN.ThetaWindows.openPrimes (n^3) ((n+1)^3)).card:ℝ)) := rfl
example : IEANTN.ThetaWindows.openPrimes = (fun a b:ℝ=>(Nat.primesLE ⌊b⌋₊).filter fun p : ℕ=>a<(p:ℝ) ∧ (p:ℝ)<b) := rfl
