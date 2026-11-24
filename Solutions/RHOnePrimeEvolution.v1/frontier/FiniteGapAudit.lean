/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import FiniteGapBridge

open Lean Elab Command

private partial def parameterUses : Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []

run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    unless modName.toString == "FiniteGapBridge" do continue
    let some (.thmInfo info) := env.find? name | continue
    let axs ← collectAxioms name
    unless axs.all allowed.contains do throwError "Unapproved finite-gap axiom {name}: {axs}"
    for (n, used) in parameterUses info.value do
      if #["hgap", "hQ"].contains n && !used then
        throwError "Unused finite source parameter {name}: {n}"
    logInfo m!"RH_FINITE_GAP_THEOREM {name} {axs}"
    count := count + 1
  unless count ≥ 7 do throwError "Missing finite-gap theorem inventory: {count}"
  let edges := #[
    (`RHOnePrime.FiniteGap.prime_in_real_interval, `RHOnePrime.FiniteGap.real_bracketing_primes),
    (`RHOnePrime.FiniteGap.fixed_gap_one_prime, `RHOnePrime.FiniteGap.prime_in_real_interval),
    (`RHOnePrime.FiniteGap.fixed_gap_one_prime, `RHOnePrime.FiniteGap.width_exceeds_1550),
    (`RHOnePrime.FiniteGap.finite_exp24_exp44_bridge, `RHOnePrime.FiniteGap.fixed_gap_one_prime),
    (`RHOnePrime.FiniteGap.finite_exp24_exp44_bridge, `RHOnePrime.FiniteGap.exp44_lt_terminal)]
  for (consumer, provider) in edges do
    let some (.thmInfo info) := env.find? consumer | throwError "Missing consumer {consumer}"
    unless info.value.getUsedConstants.contains provider do
      throwError "Missing consumed finite gap edge {consumer} -> {provider}"
    logInfo m!"RH_FINITE_GAP_VALUE_EDGE {consumer} -> {provider}"
  logInfo m!"RH_FINITE_GAP_AUDIT_PASS theorems={count} edges={edges.size}"
