/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import Lean
import GoldbachV3Consumer
import PrimeQuantileV4Consumer
import HybridSharperPrimeFrontier

open Lean Elab Command
private partial def parameterUses : Expr → List (String × Bool)
  | .lam n _ body _ => (n.toString, body.hasLooseBVar 0) :: parameterUses body
  | .mdata _ body => parameterUses body
  | _ => []

run_cmd do
  let env ← getEnv
  let roots := #[`Goldbach.v3.challenge_sorted_count_extended,
    `Goldbach.v3.challenge_sorted_count_full_finite_range,
    `Goldbach.v3.challenge_sorted_count_750m_band,
    `PrimeQuantile.v4.challenge_strict_generic_block,
    `PrimeQuantile.v4.challenge_strict_special_block,
    `PrimeQuantile.v4.challenge_shifted_sqrt_block,
    `RHOnePrime.Hybrid.all_real_open_08768,
    `RHOnePrime.Hybrid.piecewise_open_frontier,
    `RHOnePrime.Hybrid.piecewise_strictly_shorter_than_088]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for root in roots do
    let some (.thmInfo info) := env.find? root | throwError "Missing actual endpoint {root}"
    let axs ← collectAxioms root
    unless axs.all allowed.contains do throwError "Unapproved transitive axiom {root}: {axs}"
    for (name, used) in parameterUses info.value do
      if #["hi", "hgap", "hCMS", "rh"].contains name && !used then
        throwError "Unconsumed actual source parameter {root}:{name}"
    logInfo m!"RH_CANONICAL_FRONTIER_ROOT {root} {axs}"
  let edges := #[
    (`Goldbach.v3.challenge_sorted_count_extended, `RHOnePrime.Canonical.extended_from_family),
    (`Goldbach.v3.challenge_sorted_count_full_finite_range, `RHOnePrime.Canonical.full_range_from_family),
    (`Goldbach.v3.challenge_sorted_count_750m_band, `RHOnePrime.Canonical.numeric_band_from_family),
    (`PrimeQuantile.v4.challenge_strict_generic_block, `RHOnePrime.Canonical.generic_block_from_family),
    (`PrimeQuantile.v4.challenge_shifted_sqrt_block, `RHOnePrime.Canonical.shifted_block_from_family),
    (`PrimeQuantile.v4.challenge_strict_special_block, `RHOnePrime.Frontier.quantile_open_of_card),
    (`RHOnePrime.Canonical.extended_from_family, `RHOnePrime.Goldbach.window_card_le_two_sortedTriples),
    (`RHOnePrime.Canonical.full_range_from_family, `RHOnePrime.Goldbach.window_card_le_three_sortedTriples),
    (`RHOnePrime.Canonical.shifted_block_from_family, `RHOnePrime.Frontier.population_one_window_identity),
    (`RHOnePrime.Hybrid.all_real_open_08768, `RHOnePrime.Hybrid.hybrid_from_late_open),
    (`RHOnePrime.Hybrid.all_real_open_08768, `RHOnePrime.CMSSharper.open_prime_08768),
    (`RHOnePrime.Hybrid.piecewise_open_frontier, `RHOnePrime.FiniteGap.finite_constant_window),
    (`RHOnePrime.Hybrid.piecewise_open_frontier, `RHOnePrime.CMSOpen.open_prime_08301),
    (`RHOnePrime.Hybrid.piecewise_open_frontier, `RHOnePrime.CMSSharper.open_prime_08768)]
  for (consumer, provider) in edges do
    let some (.thmInfo info) := env.find? consumer | throwError "Missing consumer {consumer}"
    unless info.value.getUsedConstants.contains provider do
      throwError "Missing proof-value edge {consumer}->{provider}"
    logInfo m!"RH_CANONICAL_FRONTIER_EDGE {consumer}->{provider}"
  logInfo m!"RH_CANONICAL_FRONTIER_AUDIT_PASS roots={roots.size} edges={edges.size}"

/-- Exact generated-challenge contracts, independent of theorem display defaults. -/
example : PrimeInterval.v4.optimized_strict_family → Goldbach.v3.sorted_count_extended :=
  Goldbach.v3.challenge_sorted_count_extended
example : PrimeInterval.v4.optimized_strict_family → Goldbach.v3.sorted_count_full_finite_range :=
  Goldbach.v3.challenge_sorted_count_full_finite_range
example : PrimeInterval.v4.optimized_strict_family → Goldbach.v3.sorted_count_750m_band :=
  Goldbach.v3.challenge_sorted_count_750m_band
example : PrimeInterval.v4.optimized_strict_family → PrimeQuantile.v4.strict_generic_block :=
  PrimeQuantile.v4.challenge_strict_generic_block
example : PrimeInterval.v4.optimized_strict_215 → PrimeQuantile.v4.strict_special_block :=
  PrimeQuantile.v4.challenge_strict_special_block
example : PrimeInterval.v4.optimized_strict_family → PrimeQuantile.v4.shifted_sqrt_block :=
  PrimeQuantile.v4.challenge_shifted_sqrt_block
