/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import ZeroEnvelopeSolution
open Lean Elab Command
private partial def leadingUses : Expr → List (String × Bool)
  | .lam n _ b _ => (n.toString,b.hasLooseBVar 0)::leadingUses b
  | .mdata _ b => leadingUses b
  | _ => []
run_cmd do
  let env ← getEnv
  let targets := #[
    (`ZeroCountEnvelope.v1.literal_source_main,`Real.log_div,#["hT"]),
    (`ZeroCountEnvelope.v1.challenge_off_ordinate_envelope,`RH080.Estimates.ZeroEnvelope.recenter,#["hBPT","h₁","h₂"]),
    (`ZeroCountEnvelope.v1.challenge_bpt_better_low,`RH080.Estimates.ZeroEnvelope.bpt_better_low,#[]),
    (`ZeroCountEnvelope.v1.challenge_bw_second_better_high,`RH080.Estimates.ZeroEnvelope.bw_second_better_high,#[]),
    (`ZeroCountEnvelope.v1.challenge_bw_first_better_high,`RH080.Estimates.ZeroEnvelope.bw_first_better_high,#[])]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  for (root,provider,parameters) in targets do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual theorem {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Nonstandard axiom in {root}: {axs}"
    let constants:=info.value.getUsedConstants
    unless constants.contains provider do throwError "Expected actual provider missing {root}->{provider}"
    let uses:=leadingUses info.value
    for p in parameters do
      unless uses.any (fun r=>r.1==p && r.2) do throwError "Source input not consumed {root}:{p}"
    logInfo m!"ZERO_ENVELOPE_AUDIT {Json.mkObj [("root",toJson root.toString),("provider",toJson provider.toString),("axioms",toJson (axs.map Name.toString)),("input_uses",toJson (uses.map fun (n,u)=>Json.mkObj [("parameter",toJson n),("used",toJson u)])),("value_constants",toJson (constants.map Name.toString))]}"
  logInfo "ZERO_ENVELOPE_AUDIT_PASS_5"
example : BPTOffOrdinate.v1.bound → BellottiWongZeroCount.v1.bound_first → BellottiWongZeroCount.v1.bound_second → ZeroCountEnvelope.v1.off_ordinate_envelope := ZeroCountEnvelope.v1.challenge_off_ordinate_envelope
example : ZeroCountEnvelope.v1.bpt_better_low := ZeroCountEnvelope.v1.challenge_bpt_better_low
example : ZeroCountEnvelope.v1.bw_second_better_high := ZeroCountEnvelope.v1.challenge_bw_second_better_high
example : ZeroCountEnvelope.v1.bw_first_better_high := ZeroCountEnvelope.v1.challenge_bw_first_better_high
example : BellottiWongZeroCount.v1.bound_first=(∀ T:ℝ,Real.exp 1≤T → |ZeroCount.v1.zetaNClosed T-BellottiWongZeroCount.v1.mainWithoutConstant T|≤(2519/25000:ℝ)*Real.log T+(1223/5000:ℝ)*Real.log (Real.log T)+202086/25000) := rfl
example : ZeroCountEnvelope.v1.bwSecondAllowance=(fun L:ℝ=>(14/125:ℝ)*L+(12567/100000:ℝ)*Real.log L+464917/100000) := rfl
