/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import GoldbachNumericalBand
import HybridPrimeFrontier

open Lean Elab Command

private partial def parameterUses : Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []

run_cmd do
  let env ← getEnv
  let modules := #["PopulationFrontier", "GoldbachExtendedRange", "GoldbachNumericalBand",
    "FiniteGapBridge", "FiniteGapSourceConsumer", "FiniteGapRefined", "HybridPrimeFrontier"]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, idx) in env.const2ModIdx.toList do
    let modName := (env.header.moduleNames[idx.toNat]?).getD .anonymous
    unless modules.contains modName.toString do continue
    let some (.thmInfo info) := env.find? name | continue
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "Unapproved transitive axiom: {name}: {axioms}"
    let parameters := (parameterUses info.value).map fun (n, used) =>
      Json.mkObj [("name", toJson n), ("used_in_body", toJson used)]
    for (n, used) in parameterUses info.value do
      if #["hG", "hN", "hB", "rh", "hEven", "hgap", "hQ", "hCMS"].contains n && !used then
        throwError "Unused source/input parameter in actual proof value {name}: {n}"
    logInfo m!"RH_FRONTIER_THEOREM {Json.compress <| Json.mkObj [
      ("name",toJson name.toString), ("module",toJson modName.toString),
      ("axioms",toJson (axioms.map Name.toString)),
      ("parameters",toJson parameters)]}"
    count := count + 1
  unless count ≥ 20 do throwError "Missing frontier theorem inventory: {count}"
  let edges := #[
    (`RHOnePrime.Frontier.count_frontier, `RHOcticPush.OptimizedFinal.strict_count_family),
    (`RHOnePrime.Frontier.prime_block_frontier, `RHOcticPush.OptimizedFinal.strict_count_family),
    (`RHOnePrime.Frontier.prime_block_frontier, `RHOnePrime.Frontier.quantile_open_of_card),
    (`RHOnePrime.Frontier.pointwise_index_frontier, `RHOnePrime.Frontier.prime_block_frontier),
    (`RHOnePrime.Frontier.clamped_index_frontier, `RHOnePrime.Frontier.prime_block_frontier),
    (`RHOnePrime.Frontier.special_prime_block_open, `RHOcticPush.OptimizedFinal.strict_count_215),
    (`RHOnePrime.Frontier.effective_index_frontier, `RHOnePrime.Frontier.clamped_index_frontier),
    (`RHOnePrime.Frontier.effective_index_frontier, `RHOnePrime.Frontier.special_prime_block_open),
    (`RHOnePrime.Frontier.rich_shifted_window, `RHOnePrime.Frontier.shifted_population_frontier),
    (`RHOnePrime.Frontier.shifted_sqrt_block, `RHOnePrime.Frontier.rich_shifted_window),
    (`RHOnePrime.Frontier.shifted_sqrt_block, `RHOnePrime.Frontier.quantile_open_of_card),
    (`RHOnePrime.Goldbach.triple_containing_prime, `RHOcticPush.Goldbach.choose_sorted_pair),
    (`RHOnePrime.Goldbach.triple_large_components, `RHOnePrime.Goldbach.triple_containing_prime),
    (`RHOnePrime.Goldbach.card_le_two_sortedTriples, `RHOnePrime.Goldbach.triple_large_components),
    (`RHOnePrime.Goldbach.card_le_three_sortedTriples, `RHOnePrime.Goldbach.triple_containing_prime),
    (`RHOnePrime.Goldbach.triples_extended_range, `RHOcticPush.OptimizedFinal.strict_count_family),
    (`RHOnePrime.Goldbach.triples_extended_range, `RHOnePrime.Goldbach.window_card_le_two_sortedTriples),
    (`RHOnePrime.Goldbach.triples_full_finite_range, `RHOcticPush.OptimizedFinal.strict_count_family),
    (`RHOnePrime.Goldbach.triples_full_finite_range, `RHOnePrime.Goldbach.window_card_le_three_sortedTriples),
    (`RHOnePrime.Goldbach.triples_no_loss_range, `RHOcticPush.OptimizedFinal.strict_count_family),
    (`RHOnePrime.Goldbach.triples_piecewise_frontier, `RHOnePrime.Goldbach.triples_no_loss_range),
    (`RHOnePrime.Goldbach.triples_piecewise_frontier, `RHOnePrime.Goldbach.triples_extended_range),
    (`RHOnePrime.Goldbach.triples_piecewise_frontier, `RHOnePrime.Goldbach.triples_full_finite_range),
    (`RHOnePrime.Goldbach.triples_shifted_frontier, `RHOnePrime.Goldbach.triples_piecewise_frontier),
    (`RHOnePrime.Goldbach.triples_750_million_new_band, `RHOnePrime.Goldbach.triples_extended_214891875),
    (`RHOnePrime.FiniteGap.source_gap_exp24_exp44_bridge, `RHOnePrimeEvolution.FiniteEndpoint.terminal_prime),
    (`RHOnePrime.FiniteGap.source_gap_exp24_exp44_bridge, `RHOnePrime.FiniteGap.source_gap_to_terminal),
    (`RHOnePrime.FiniteGap.finite_coefficient_0004, `RHOnePrimeEvolution.FiniteEndpoint.terminal_prime),
    (`RHOnePrime.FiniteGap.finite_coefficient_0004, `RHOnePrime.FiniteGap.width_exceeds_1550_refined),
    (`RHOnePrime.Hybrid.hybrid_from_late_open, `RHOnePrime.FiniteGap.finite_coefficient_0004),
    (`RHOnePrime.Hybrid.all_real_open_08771, `RHOnePrime.Hybrid.hybrid_from_late_open),
    (`RHOnePrime.Hybrid.all_real_open_08771, `RHOnePrime.CMSOpen.open_prime_08771)]
  for (consumer, provider) in edges do
    let some (.thmInfo info) := env.find? consumer | throwError "Missing consumer {consumer}"
    unless info.value.getUsedConstants.contains provider do
      throwError "Missing actual proof-value edge {consumer} -> {provider}"
    logInfo m!"RH_FRONTIER_VALUE_EDGE {consumer} -> {provider}"
  logInfo m!"RH_FRONTIER_AUDIT_PASS theorems={count} edges={edges.size}"

#check @RHOnePrime.Frontier.count_frontier
#check @RHOnePrime.Frontier.quantile_open_of_card
#check @RHOnePrime.Frontier.pointwise_index_frontier
#check @RHOnePrime.Goldbach.triples_extended_range
#check @RHOnePrime.Goldbach.triples_full_finite_range
#check @RHOnePrime.Goldbach.triples_piecewise_frontier
